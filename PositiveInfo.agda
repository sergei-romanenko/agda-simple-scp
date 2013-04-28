module PositiveInfo where

open import Data.List
open import Data.Empty
open import Data.Unit

open import Relation.Binary.PropositionalEquality
  renaming([_] to [_]ⁱ)

open import Function

open ≡-Reasoning

open import Util
open import ExpLang

-- setNilAt

setNilAt : (sels : List Selector) → NTrm

setNilAt sels =
  replaceAt sels (⟪_⟫ⁿ []) []ⁿ

-- setConsAt

setConsAt : (sels : List Selector) → NTrm

setConsAt sels = 
  replaceAt sels (⟪_⟫ⁿ []) 
    (⟪_⟫ⁿ (sels ++ [ HD ]) ∷ⁿ ⟪_⟫ⁿ (sels ++ [ TL ]))


-- propagateIfCond

propagateIfCond : (nt : NTrm) → NTrm

propagateIfCond []ⁿ = []ⁿ
propagateIfCond (nt1 ∷ⁿ nt2) =
  propagateIfCond nt1 ∷ⁿ propagateIfCond nt2
propagateIfCond (⟪_⟫ⁿ sels) = ⟪_⟫ⁿ sels
propagateIfCond (IfNilⁿ sels nt1 nt2) =
  IfNilⁿ sels
    (normNCmp (propagateIfCond nt1) (setNilAt sels))
    (normNCmp (propagateIfCond nt2) (setConsAt sels))
propagateIfCond ↯ⁿ = ↯ⁿ

-- Establishing the correctness of `propagateIfCond` is once again decomposed
-- into a sequence of lemmas. 

-- setNilAtPreservesEval′

setNilAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 (⟪_⟫ⁿ sels2) []ⁿ
    ≡ normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ []) []ⁿ) sels2

setNilAtPreservesEval′ [] sels2 = refl

setNilAtPreservesEval′ (HD ∷ sels1) sels2 =
  begin
    replaceAt (HD ∷ sels1) (⟪_⟫ⁿ sels2) []ⁿ
      ≡⟨ refl ⟩
    replaceAt sels1 (⟪_⟫ⁿ (sels2 ++ [ HD ])) []ⁿ ∷ⁿ
      ⟪_⟫ⁿ (sels2 ++ [ TL ])
      ≡⟨ cong (flip _∷ⁿ_ (⟪_⟫ⁿ (sels2 ++ [ TL ])))
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ HD ])) ⟩
    normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ []) []ⁿ) (sels2 ++ [ HD ]) ∷ⁿ
      ⟪_⟫ⁿ (sels2 ++ [ TL ])
      ≡⟨ cong (flip _∷ⁿ_ (⟪_⟫ⁿ (sels2 ++ [ TL ])))
              (normNCmpSels∘++ (replaceAt sels1 (⟪_⟫ⁿ []) []ⁿ)
                               sels2 [ HD ]) ⟩
    normNCmpSels
      (normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ []) []ⁿ) [ HD ]) sels2 ∷ⁿ
        (⟪_⟫ⁿ (sels2 ++ [ TL ]))
      ≡⟨ cong (flip _∷ⁿ_ (⟪_⟫ⁿ (sels2 ++ [ TL ])))
              (cong (flip normNCmpSels sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ HD ])) ⟩
    normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ [ HD ]) []ⁿ) sels2 ∷ⁿ
      ⟪_⟫ⁿ (sels2 ++ [ TL ])
      ≡⟨ refl ⟩
    normNCmpSels (replaceAt (HD ∷ sels1) (⟪_⟫ⁿ []) []ⁿ) sels2
  ∎

setNilAtPreservesEval′ (TL ∷ sels1) sels2 =
  begin
    replaceAt (TL ∷ sels1) (⟪_⟫ⁿ sels2) []ⁿ
      ≡⟨ refl ⟩
    ⟪_⟫ⁿ (sels2 ++ [ HD ]) ∷ⁿ
      replaceAt sels1 (⟪_⟫ⁿ (sels2 ++ [ TL ])) []ⁿ
      ≡⟨ cong (_∷ⁿ_ (⟪_⟫ⁿ (sels2 ++ [ HD ])))
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ TL ])) ⟩
    ⟪_⟫ⁿ (sels2 ++ [ HD ]) ∷ⁿ
      normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ []) []ⁿ) (sels2 ++ [ TL ])
      ≡⟨ cong (_∷ⁿ_ (⟪_⟫ⁿ (sels2 ++ [ HD ])))
              (normNCmpSels∘++ (replaceAt sels1 (⟪_⟫ⁿ []) []ⁿ)
                               sels2 (TL ∷ [])) ⟩
    ⟪_⟫ⁿ (sels2 ++ [ HD ]) ∷ⁿ
      normNCmpSels
            (normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ []) []ⁿ) [ TL ]) sels2
      ≡⟨ cong (_∷ⁿ_ (⟪_⟫ⁿ (sels2 ++ [ HD ])))
              (cong (flip normNCmpSels sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ TL ])) ⟩
    ⟪_⟫ⁿ (sels2 ++ [ HD ]) ∷ⁿ
      normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ [ TL ]) []ⁿ) sels2
      ≡⟨ refl ⟩
    normNCmpSels (replaceAt (TL ∷ sels1) (⟪_⟫ⁿ []) []ⁿ) sels2
  ∎

-- setConsAtPreservesEval′

setConsAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 (⟪_⟫ⁿ sels2)
            (⟪_⟫ⁿ (sels2 ++ sels1 ++ [ HD ]) ∷ⁿ
              ⟪_⟫ⁿ (sels2 ++ sels1 ++ [ TL ]))
  ≡
  normNCmpSels (replaceAt sels1 (⟪_⟫ⁿ [])
                          (⟪_⟫ⁿ (sels1 ++ [ HD ]) ∷ⁿ
                            ⟪_⟫ⁿ (sels1 ++ [ TL ])))
               sels2

setConsAtPreservesEval′ [] sels2 = refl

setConsAtPreservesEval′ (HD ∷ sels1) sels2
  rewrite sym $ ++-assoc sels2 [ HD ] (sels1 ++ [ HD ])
        | sym $ ++-assoc sels2 [ HD ] (sels1 ++ [ TL ])
  = cong (flip _∷ⁿ_ (⟪_⟫ⁿ (sels2 ++ [ TL ])))
         helper
  where
    helper = begin
      replaceAt sels1 (⟪_⟫ⁿ (sels2 ++ [ HD ]))
          (⟪_⟫ⁿ ((sels2 ++ [ HD ]) ++ sels1 ++ [ HD ]) ∷ⁿ
            ⟪_⟫ⁿ ((sels2 ++ [ HD ]) ++ sels1 ++ [ TL ]))
        ≡⟨ setConsAtPreservesEval′ sels1 (sels2 ++ [ HD ]) ⟩
      normNCmpSels
          (replaceAt sels1 (⟪_⟫ⁿ [])
              (⟪_⟫ⁿ (sels1 ++ [ HD ]) ∷ⁿ ⟪_⟫ⁿ (sels1 ++ [ TL ])))
          (sels2 ++ [ HD ])
        ≡⟨ normNCmpSels∘++
             (replaceAt sels1 (⟪_⟫ⁿ [])
               (⟪_⟫ⁿ (sels1 ++ [ HD ]) ∷ⁿ ⟪_⟫ⁿ (sels1 ++ [ TL ])))
             sels2 (HD ∷ []) ⟩
      normNCmpSels
        (normNCmpSels
          (replaceAt sels1 (⟪_⟫ⁿ [])
                     (⟪_⟫ⁿ (sels1 ++ [ HD ]) ∷ⁿ ⟪_⟫ⁿ (sels1 ++ [ TL ])))
          (HD ∷ []))
        sels2
        ≡⟨ cong (flip normNCmpSels sels2)
                (sym $ setConsAtPreservesEval′ sels1 [ HD ]) ⟩
      normNCmpSels
          (replaceAt sels1 (⟪_⟫ⁿ [ HD ])
            ((⟪_⟫ⁿ ([ HD ] ++ sels1 ++ [ HD ])) ∷ⁿ
              ⟪_⟫ⁿ ([ HD ] ++ sels1 ++ [ TL ])))
          sels2
      ∎

setConsAtPreservesEval′ (TL ∷ sels1) sels2
  rewrite sym $ ++-assoc sels2 [ TL ] (sels1 ++ [ TL ])
        | sym $ ++-assoc sels2 [ TL ] (sels1 ++ [ HD ])
        | setConsAtPreservesEval′ sels1 (sels2 ++ [ TL ])
        | setConsAtPreservesEval′ sels1 [ TL ]
        | normNCmpSels∘++
             (replaceAt sels1 (⟪_⟫ⁿ [])
               (⟪_⟫ⁿ (sels1 ++ [ HD ]) ∷ⁿ ⟪_⟫ⁿ (sels1 ++ [ TL ])))
             sels2 (TL ∷ [])

  = refl

-- setNilAtPreservesEval′′

setNilAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  ⟦⌈ setNilAt (sels1 ++ sels2) ⌉⟧ v !! sels1
    ≡ ⟦⌈ setNilAt sels2 ⌉⟧ (v !! sels1)

setNilAtPreservesEval′′ v sels1 sels2 = begin
  (⟦⌈ setNilAt (sels1 ++ sels2) ⌉⟧ v) !! sels1
    ≡⟨ refl ⟩
  (⟦⌈ (replaceAt (sels1 ++ sels2) (⟪_⟫ⁿ []) []ⁿ) ⌉⟧ v) !! sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘normSelsNCmp
               (replaceAt (sels1 ++ sels2) (⟪_⟫ⁿ []) []ⁿ) sels1 v ⟩
  ⟦⌈ normSelsNCmp (replaceAt (sels1 ++ sels2) (⟪_⟫ⁿ []) []ⁿ) sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip normSelsNCmp sels1)
                  (replaceAt∘++ sels1 sels2 (⟪_⟫ⁿ []) []ⁿ)) ⟩
  ⟦⌈ normSelsNCmp (replaceAt sels1 (⟪_⟫ⁿ [])
                    (replaceAt sels2 (normSelsNCmp (⟪_⟫ⁿ []) sels1) []ⁿ))
                       sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (normSelsNCmp∘replaceAt sels1 (⟪_⟫ⁿ [])
              (replaceAt sels2 (normSelsNCmp (⟪_⟫ⁿ []) sels1) []ⁿ)) ⟩
  ⟦⌈ replaceAt sels2 (normSelsNCmp (⟪_⟫ⁿ []) sels1) []ⁿ ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip (replaceAt sels2) []ⁿ)
                  (normSelsNCmp∘⟪⟫ⁿ [] sels1)) ⟩
  ⟦⌈ replaceAt sels2 (⟪_⟫ⁿ sels1) []ⁿ ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v) (setNilAtPreservesEval′ sels2 sels1) ⟩
  ⟦⌈ normNCmpSels (replaceAt sels2 (⟪_⟫ⁿ []) []ⁿ) sels1 ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘normNCmpSels (replaceAt sels2 (⟪_⟫ⁿ []) []ⁿ) sels1 v ⟩
  ⟦⌈ replaceAt sels2 (⟪_⟫ⁿ []) []ⁿ ⌉⟧ (v !! sels1)
    ≡⟨ refl ⟩
  ⟦⌈ setNilAt sels2 ⌉⟧ (v !! sels1)
  ∎

-- setConsAtPreservesEval′′

setConsAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  ⟦⌈ setConsAt (sels1 ++ sels2) ⌉⟧ v !! sels1
    ≡ ⟦⌈ setConsAt sels2 ⌉⟧ (v !! sels1)

setConsAtPreservesEval′′ v sels1 sels2 = begin
  ⟦⌈ setConsAt (sels1 ++ sels2) ⌉⟧ v !! sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘normSelsNCmp (setConsAt (sels1 ++ sels2)) sels1 v ⟩
  ⟦⌈ normSelsNCmp (setConsAt (sels1 ++ sels2)) sels1 ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ normSelsNCmp (replaceAt (sels1 ++ sels2) (⟪_⟫ⁿ [])
                          (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                            ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])))
                       sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip normSelsNCmp sels1)
                  (replaceAt∘++ sels1 sels2 (⟪_⟫ⁿ [])
                    (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                      ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])))) ⟩
  ⟦⌈ normSelsNCmp
           (replaceAt sels1 (⟪_⟫ⁿ [])
             (replaceAt sels2 (normSelsNCmp (⟪_⟫ⁿ []) sels1)
                        (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                          ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ]))))
           sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (normSelsNCmp∘replaceAt sels1 (⟪_⟫ⁿ [])
              (replaceAt sels2 (normSelsNCmp (⟪_⟫ⁿ []) sels1)
                         (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                           ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])))) ⟩
  ⟦⌈ replaceAt sels2 (normSelsNCmp (⟪_⟫ⁿ []) sels1)
            (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
              ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip (replaceAt sels2)
                        (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                          ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])))
                  (normSelsNCmp∘⟪⟫ⁿ [] sels1)) ⟩
  ⟦⌈ replaceAt sels2
                    (⟪_⟫ⁿ sels1)
                    (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                      ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (replaceAt sels2 (⟪_⟫ⁿ sels1))
                  (cong (flip _∷ⁿ_ (⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])))
                        (cong ⟪_⟫ⁿ (++-assoc sels1 sels2 [ HD ])))) ⟩
  ⟦⌈ replaceAt sels2
               (⟪_⟫ⁿ sels1)
                 (⟪_⟫ⁿ (sels1 ++ sels2 ++ [ HD ]) ∷ⁿ
                   ⟪_⟫ⁿ ((sels1 ++ sels2) ++ [ TL ])) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (replaceAt sels2 (⟪_⟫ⁿ sels1))
                  (cong (_∷ⁿ_ (⟪_⟫ⁿ (sels1 ++ sels2 ++ [ HD ])))
                        (cong ⟪_⟫ⁿ (++-assoc sels1 sels2 [ TL ])))) ⟩
  ⟦⌈ replaceAt sels2
               (⟪_⟫ⁿ sels1)
               (⟪_⟫ⁿ (sels1 ++ sels2 ++ [ HD ]) ∷ⁿ
                 ⟪_⟫ⁿ (sels1 ++ sels2 ++ [ TL ])) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (setConsAtPreservesEval′ sels2 sels1) ⟩
  ⟦⌈ normNCmpSels (replaceAt sels2 (⟪_⟫ⁿ [])
                             (⟪_⟫ⁿ (sels2 ++ [ HD ]) ∷ⁿ
                               ⟪_⟫ⁿ (sels2 ++ [ TL ])))
            sels1 ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ normNCmpSels (setConsAt sels2) sels1 ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘normNCmpSels (setConsAt sels2) sels1 v ⟩
  ⟦⌈ setConsAt sels2 ⌉⟧ (v !! sels1)
  ∎

-- Auxiliaries

↯ˣ≢[]ˣ : ↯ˣ ≢ []ˣ
↯ˣ≢[]ˣ = λ ()

∷ˣ≢[]ˣ : ∀ {v1 v2} → v1 ∷ˣ v2 ≢ []ˣ
∷ˣ≢[]ˣ = λ ()

∷ˣ≢↯ˣ : ∀ {v1 v2} → v1 ∷ˣ v2 ≢ ↯ˣ
∷ˣ≢↯ˣ = λ ()

-- ⟦⌈⌉⟧∘setNilAt

⟦⌈⌉⟧∘setNilAt : (sels : List Selector) (v : Val) →
  v !! sels ≡ []ˣ → ⟦⌈ setNilAt sels ⌉⟧ v ≡ v

⟦⌈⌉⟧∘setNilAt [] []ˣ h = refl

⟦⌈⌉⟧∘setNilAt (sel ∷ sels) []ˣ h
  rewrite !!-↯ˣ sels
  = ⊥-elim (↯ˣ≢[]ˣ h)

⟦⌈⌉⟧∘setNilAt [] (v1 ∷ˣ v2) h =
  ⊥-elim (∷ˣ≢[]ˣ h)

⟦⌈⌉⟧∘setNilAt (HD ∷ sels) (v1 ∷ˣ v2) h =
  cong (flip _∷ˣ_ v2) helper
  where
  helper = begin
    ⟦⌈ replaceAt sels (⟪_⟫ⁿ [ HD ]) []ⁿ ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ HD ] []ⁿ) ⟩
    ⟦⌈ normSelsNCmp (replaceAt ([ HD ] ++ sels) (⟪_⟫ⁿ []) []ⁿ) [ HD ] ⌉⟧
         (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ HD ] ++ sels) (⟪_⟫ⁿ []) []ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ HD ]
      ≡⟨ refl ⟩
    ⟦⌈ setNilAt ([ HD ] ++ sels) ⌉⟧ (v1 ∷ˣ v2) !! [ HD ]
      ≡⟨ setNilAtPreservesEval′′ (v1 ∷ˣ v2) [ HD ] sels ⟩
    ⟦⌈ setNilAt sels ⌉⟧ (v1 ∷ˣ v2 !! [ HD ])
      ≡⟨ refl ⟩
    ⟦⌈ setNilAt sels ⌉⟧ v1
      ≡⟨ ⟦⌈⌉⟧∘setNilAt sels v1 h ⟩
    v1
    ∎

⟦⌈⌉⟧∘setNilAt (TL ∷ sels) (v1 ∷ˣ v2) h =
  cong (_∷ˣ_ v1) helper
  where
  helper = begin
    ⟦⌈ replaceAt sels (⟪_⟫ⁿ [ TL ]) []ⁿ ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ TL ] []ⁿ) ⟩
    ⟦⌈ normSelsNCmp (replaceAt ([ TL ] ++ sels) (⟪_⟫ⁿ []) []ⁿ) [ TL ] ⌉⟧
         (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ TL ] ++ sels) (⟪_⟫ⁿ []) []ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ TL ]
      ≡⟨ refl ⟩
    ⟦⌈ setNilAt ([ TL ] ++ sels) ⌉⟧ (v1 ∷ˣ v2) !! [ TL ]
      ≡⟨ setNilAtPreservesEval′′ (v1 ∷ˣ v2) [ TL ] sels ⟩
    ⟦⌈ setNilAt sels ⌉⟧ (v1 ∷ˣ v2 !! [ TL ])
      ≡⟨ refl ⟩
    ⟦⌈ setNilAt sels ⌉⟧ v2
      ≡⟨ ⟦⌈⌉⟧∘setNilAt sels v2 h ⟩
    v2
    ∎

⟦⌈⌉⟧∘setNilAt sels ↯ˣ h
  rewrite !!-↯ˣ sels
  = ⊥-elim (↯ˣ≢[]ˣ h)

-- ⟦⌈⌉⟧∘setConsAt

⟦⌈⌉⟧∘setConsAt : (sels : List Selector) (v : Val) {u1 u2 : Val} →
  v !! sels ≡ u1 ∷ˣ u2 → ⟦⌈ setConsAt sels ⌉⟧ v ≡ v

⟦⌈⌉⟧∘setConsAt [] []ˣ h = ⊥-elim (∷ˣ≢[]ˣ (sym h))

⟦⌈⌉⟧∘setConsAt (sel ∷ sels) []ˣ h
  rewrite !!-↯ˣ sels
  = ⊥-elim (∷ˣ≢↯ˣ (sym h))

⟦⌈⌉⟧∘setConsAt [] (v1 ∷ˣ v2) h = refl

⟦⌈⌉⟧∘setConsAt (HD ∷ sels) (v1 ∷ˣ v2) h =
  cong (flip _∷ˣ_ v2) helper
  where
  helper = begin
    ⟦⌈ replaceAt sels (⟪_⟫ⁿ [ HD ])
                      (⟪_⟫ⁿ ((HD ∷ sels) ++ [ HD ]) ∷ⁿ
                        ⟪_⟫ⁿ ((HD ∷ sels) ++ [ TL ])) ⌉⟧
      (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ HD ]
                                 (⟪_⟫ⁿ (HD ∷ sels ++ [ HD ]) ∷ⁿ
                                   ⟪_⟫ⁿ (HD ∷ sels ++ [ TL ]))) ⟩
    ⟦⌈ normSelsNCmp (replaceAt ([ HD ] ++ sels) (⟪_⟫ⁿ [])
                                    (⟪_⟫ⁿ (HD ∷ sels ++ [ HD ]) ∷ⁿ
                                      ⟪_⟫ⁿ (HD ∷ sels ++ [ TL ])))
                         [ HD ] ⌉⟧
           (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ HD ] ++ sels) (⟪_⟫ⁿ [])
                                  (⟪_⟫ⁿ (HD ∷ sels ++ [ HD ]) ∷ⁿ
                                    ⟪_⟫ⁿ (HD ∷ sels ++ [ TL ])) ⌉⟧
                     (v1 ∷ˣ v2)
             !! [ HD ]
      ≡⟨ refl ⟩
    ⟦⌈ setConsAt ([ HD ] ++ sels) ⌉⟧ (v1 ∷ˣ v2) !! [ HD ]
      ≡⟨ setConsAtPreservesEval′′ (v1 ∷ˣ v2) (HD ∷ []) sels ⟩
    ⟦⌈ setConsAt sels ⌉⟧ (v1 !! [])
      ≡⟨ refl ⟩
    ⟦⌈ setConsAt sels ⌉⟧ v1
      ≡⟨ ⟦⌈⌉⟧∘setConsAt sels v1 h ⟩
    v1
    ∎

⟦⌈⌉⟧∘setConsAt (TL ∷ sels) (v1 ∷ˣ v2) h =
  cong (_∷ˣ_ v1) helper
  where
  helper = begin
    ⟦⌈ replaceAt sels (⟪_⟫ⁿ (TL ∷ []))
                      (⟪_⟫ⁿ (TL ∷ sels ++ [ HD ]) ∷ⁿ
                         ⟪_⟫ⁿ (TL ∷ sels ++ [ TL ])) ⌉⟧
           (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ TL ]
                                 (⟪_⟫ⁿ (TL ∷ sels ++ [ HD ]) ∷ⁿ
                                   ⟪_⟫ⁿ (TL ∷ sels ++ [ TL ]))) ⟩
    ⟦⌈ normSelsNCmp (replaceAt ([ TL ] ++ sels) (⟪_⟫ⁿ [])
                                    (⟪_⟫ⁿ (TL ∷ sels ++ [ HD ]) ∷ⁿ
                                      ⟪_⟫ⁿ (TL ∷ sels ++ [ TL ])))
                         [ TL ] ⌉⟧
           (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ TL ] ++ sels) (⟪_⟫ⁿ [])
                 (⟪_⟫ⁿ (TL ∷ sels ++ [ HD ]) ∷ⁿ
                   ⟪_⟫ⁿ (TL ∷ sels ++ [ TL ])) ⌉⟧
                 (v1 ∷ˣ v2)
             !! [ TL ]
      ≡⟨ refl ⟩
    ⟦⌈ setConsAt ([ TL ] ++ sels) ⌉⟧ (v1 ∷ˣ v2) !! [ TL ]
      ≡⟨ setConsAtPreservesEval′′ (v1 ∷ˣ v2) (TL ∷ []) sels ⟩
    ⟦⌈ setConsAt sels ⌉⟧ (v2 !! [])
      ≡⟨ refl ⟩
    ⟦⌈ setConsAt sels ⌉⟧ v2
      ≡⟨ ⟦⌈⌉⟧∘setConsAt sels v2 h ⟩
    v2
    ∎

⟦⌈⌉⟧∘setConsAt sels ↯ˣ h
  rewrite  !!-↯ˣ sels
  = ⊥-elim (∷ˣ≢↯ˣ (sym h))

-- condPropagatorsPreserveEval

condPropagatorsPreserveEval :
  (sels : List Selector) (nt1 nt2 : NTrm) (v : Val) →
    ⟦⌈ IfNilⁿ sels (normNCmp nt1 (setNilAt sels))
                   (normNCmp nt2 (setConsAt sels)) ⌉⟧ v
  ≡
  ⟦⌈ IfNilⁿ sels nt1 nt2 ⌉⟧ v

condPropagatorsPreserveEval sels nt1 nt2 v
  rewrite ⟦⟧∘⟪⟫ sels v
  with v !! sels | inspect (_!!_ v) sels 

... | []ˣ | [ ≡[]ˣ ]ⁱ = begin
  ⟦⌈ normNCmp nt1 (setNilAt sels) ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘normNCmp nt1 (setNilAt sels) v ⟩
  ⟦⌈ nt1 ⌉⟧ (⟦⌈ setNilAt sels ⌉⟧ v)
    ≡⟨ cong ⟦⌈ nt1 ⌉⟧ (⟦⌈⌉⟧∘setNilAt sels v ≡[]ˣ) ⟩
  ⟦⌈ nt1 ⌉⟧ v
  ∎

... | _ ∷ˣ _ | [ ≡∷ˣ ]ⁱ = begin
  ⟦⌈ normNCmp nt2 (setConsAt sels) ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘normNCmp nt2 (setConsAt sels) v ⟩
  ⟦⌈ nt2 ⌉⟧ (⟦⌈ setConsAt sels ⌉⟧ v)
    ≡⟨ cong ⟦⌈ nt2 ⌉⟧ (⟦⌈⌉⟧∘setConsAt sels v ≡∷ˣ) ⟩
  ⟦⌈ nt2 ⌉⟧ v   
  ∎

... | ↯ˣ | _ = refl

--
-- ⟦⌈⌉⟧∘propagateIfCond
--

⟦⌈⌉⟧∘propagateIfCond : (nt : NTrm) (v : Val) →
  ⟦⌈ propagateIfCond nt ⌉⟧ v ≡ ⟦⌈ nt ⌉⟧ v

⟦⌈⌉⟧∘propagateIfCond []ⁿ v = refl

⟦⌈⌉⟧∘propagateIfCond (nt1 ∷ⁿ nt2) v
  rewrite ⟦⌈⌉⟧∘propagateIfCond nt1 v
        | ⟦⌈⌉⟧∘propagateIfCond nt2 v
 = refl

⟦⌈⌉⟧∘propagateIfCond (⟪_⟫ⁿ sels) v = refl

⟦⌈⌉⟧∘propagateIfCond (IfNilⁿ sels nt1 nt2) v = begin
  ⟦⌈ propagateIfCond (IfNilⁿ sels nt1 nt2) ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ IfNilⁿ sels (normNCmp (propagateIfCond nt1) (setNilAt sels))
                 (normNCmp (propagateIfCond nt2) (setConsAt sels)) ⌉⟧ v
    ≡⟨ refl ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ normNCmp (propagateIfCond nt1) (setNilAt sels) ⌉⟧ v)
        (⟦⌈ normNCmp (propagateIfCond nt2) (setConsAt sels) ⌉⟧ v)
    ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
             (⟦⌈⌉⟧∘normNCmp (propagateIfCond nt1) (setNilAt sels) v)
             (⟦⌈⌉⟧∘normNCmp (propagateIfCond nt2) (setConsAt sels) v) ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ propagateIfCond nt1 ⌉⟧ (⟦⌈ (setNilAt sels) ⌉⟧ v))
        (⟦⌈ propagateIfCond nt2 ⌉⟧ (⟦⌈ setConsAt sels ⌉⟧ v))
    ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
             (⟦⌈⌉⟧∘propagateIfCond nt1 (⟦⌈ setNilAt sels ⌉⟧ v))
             (⟦⌈⌉⟧∘propagateIfCond nt2 (⟦⌈ setConsAt sels ⌉⟧ v)) ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ nt1 ⌉⟧ (⟦⌈ setNilAt sels ⌉⟧ v))
        (⟦⌈ nt2 ⌉⟧ (⟦⌈ setConsAt sels ⌉⟧ v))
    ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
             (sym $ ⟦⌈⌉⟧∘normNCmp nt1 (setNilAt sels) v)
             (sym $ ⟦⌈⌉⟧∘normNCmp nt2 (setConsAt sels) v) ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ normNCmp nt1 (setNilAt sels) ⌉⟧ v)
        (⟦⌈ normNCmp nt2 (setConsAt sels) ⌉⟧ v)
    ≡⟨ refl ⟩
  ⟦⌈ IfNilⁿ sels (normNCmp nt1 (setNilAt sels))
                 (normNCmp nt2 (setConsAt sels)) ⌉⟧ v
    ≡⟨ condPropagatorsPreserveEval sels nt1 nt2 v ⟩
  ⟦⌈ IfNilⁿ sels nt1 nt2 ⌉⟧ v
  ∎

⟦⌈⌉⟧∘propagateIfCond ↯ⁿ v = refl

--
-- norm
--

-- We can combine the first two stages - normalization and
-- positive information propagation - into a single function,
-- and trivially establish its correctness.

norm : (t : Trm) → NTrm
norm t = propagateIfCond (normConv t)

-- ⟦⌈⌉⟧∘norm

⟦⌈⌉⟧∘norm : ∀ t v → ⟦⌈ norm t ⌉⟧ v ≡ ⟦ t ⟧ v

⟦⌈⌉⟧∘norm t v = begin
  ⟦⌈ norm t ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ propagateIfCond (normConv t) ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘propagateIfCond (normConv t) v ⟩
  ⟦⌈ normConv t ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘normConv t v ⟩
  ⟦ t ⟧ v
  ∎

--
