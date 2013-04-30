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
  replaceAt sels ⟪ [] ⟫ⁿ []ⁿ

-- setConsAt

setConsAt : (sels : List Selector) → NTrm

setConsAt sels = 
  replaceAt sels ⟪ [] ⟫ⁿ (⟪ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels ++ [ TL ] ⟫ⁿ)


-- propagateIfCond

propagateIfCond : (nt : NTrm) → NTrm

propagateIfCond []ⁿ = []ⁿ
propagateIfCond (nt1 ∷ⁿ nt2) =
  propagateIfCond nt1 ∷ⁿ propagateIfCond nt2
propagateIfCond ⟪ sels ⟫ⁿ = ⟪ sels ⟫ⁿ
propagateIfCond (IfNilⁿ sels nt1 nt2) =
  IfNilⁿ sels
    (propagateIfCond nt1 ○ setNilAt sels)
    (propagateIfCond nt2 ○ setConsAt sels)
propagateIfCond ↯ⁿ = ↯ⁿ

-- Establishing the correctness of `propagateIfCond` is once again decomposed
-- into a sequence of lemmas. 

-- setNilAtPreservesEval′

setNilAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 ⟪ sels2 ⟫ⁿ []ⁿ
    ≡ replaceAt sels1 ⟪ [] ⟫ⁿ []ⁿ ○⟪ sels2 ⟫ⁿ

setNilAtPreservesEval′ [] sels2 = refl

setNilAtPreservesEval′ (HD ∷ sels1) sels2 =
  begin
    replaceAt (HD ∷ sels1) ⟪ sels2 ⟫ⁿ []ⁿ
      ≡⟨ refl ⟩
    replaceAt sels1 ⟪ sels2 ++ [ HD ] ⟫ⁿ []ⁿ ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ cong (flip _∷ⁿ_ ⟪ sels2 ++ [ TL ] ⟫ⁿ)
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ HD ])) ⟩
    (replaceAt sels1 ⟪ [] ⟫ⁿ []ⁿ ○⟪ sels2 ++ [ HD ] ⟫ⁿ) ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ cong (flip _∷ⁿ_ (⟪ sels2 ++ [ TL ] ⟫ⁿ))
              (∘⟪⟫ⁿ∘++ (replaceAt sels1 ⟪ [] ⟫ⁿ []ⁿ) sels2 [ HD ]) ⟩
    (replaceAt sels1 ⟪ [] ⟫ⁿ []ⁿ ○⟪ [ HD ] ⟫ⁿ ○⟪ sels2 ⟫ⁿ) ∷ⁿ
      ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ cong (flip _∷ⁿ_ (⟪ sels2 ++ [ TL ] ⟫ⁿ))
              (cong (flip _○⟪_⟫ⁿ sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ HD ])) ⟩
    (replaceAt sels1 ⟪ [ HD ] ⟫ⁿ []ⁿ ○⟪ sels2 ⟫ⁿ) ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ refl ⟩
    replaceAt (HD ∷ sels1) ⟪ [] ⟫ⁿ []ⁿ ○⟪ sels2 ⟫ⁿ
  ∎

setNilAtPreservesEval′ (TL ∷ sels1) sels2 =
  begin
    replaceAt (TL ∷ sels1) ⟪ sels2 ⟫ⁿ []ⁿ
      ≡⟨ refl ⟩
    ⟪ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ replaceAt sels1 ⟪ sels2 ++ [ TL ] ⟫ⁿ []ⁿ
      ≡⟨ cong (_∷ⁿ_ ⟪ sels2 ++ [ HD ] ⟫ⁿ)
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ TL ])) ⟩
    ⟪ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ
      (replaceAt sels1 ⟪ [] ⟫ⁿ []ⁿ ○⟪ sels2 ++ [ TL ] ⟫ⁿ)
      ≡⟨ cong (_∷ⁿ_ ⟪ sels2 ++ [ HD ] ⟫ⁿ)
              (∘⟪⟫ⁿ∘++ (replaceAt sels1 ⟪ [] ⟫ⁿ []ⁿ)
                               sels2 (TL ∷ [])) ⟩
    ⟪ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ
      (replaceAt sels1 ⟪ [] ⟫ⁿ []ⁿ ○⟪ [ TL ] ⟫ⁿ ○⟪ sels2 ⟫ⁿ)
      ≡⟨ cong (_∷ⁿ_ ⟪ sels2 ++ [ HD ] ⟫ⁿ)
              (cong (flip _○⟪_⟫ⁿ sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ TL ])) ⟩
    ⟪ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ
      ( replaceAt sels1 ⟪ [ TL ] ⟫ⁿ []ⁿ ○⟪ sels2 ⟫ⁿ)
      ≡⟨ refl ⟩
    (replaceAt (TL ∷ sels1) ⟪ [] ⟫ⁿ []ⁿ) ○⟪ sels2 ⟫ⁿ
  ∎

-- setConsAtPreservesEval′

setConsAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 ⟪ sels2 ⟫ⁿ
            (⟪ sels2 ++ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels2 ++ sels1 ++ [ TL ] ⟫ⁿ)
  ≡
  replaceAt sels1 ⟪ [] ⟫ⁿ
            (⟪ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels1 ++ [ TL ] ⟫ⁿ) ○⟪ sels2 ⟫ⁿ 
               

setConsAtPreservesEval′ [] sels2 = refl

setConsAtPreservesEval′ (HD ∷ sels1) sels2
  rewrite sym $ LM.assoc sels2 [ HD ] (sels1 ++ [ HD ])
        | sym $ LM.assoc sels2 [ HD ] (sels1 ++ [ TL ])
  = cong (flip _∷ⁿ_ ⟪ sels2 ++ [ TL ] ⟫ⁿ)
         helper
  where
    helper = begin
      replaceAt sels1 ⟪ sels2 ++ [ HD ] ⟫ⁿ
                (⟪ (sels2 ++ [ HD ]) ++ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ
                  ⟪ (sels2 ++ [ HD ]) ++ sels1 ++ [ TL ] ⟫ⁿ)
        ≡⟨ setConsAtPreservesEval′ sels1 (sels2 ++ [ HD ]) ⟩
      replaceAt sels1 ⟪ [] ⟫ⁿ
                (⟪ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels1 ++ [ TL ] ⟫ⁿ)
                  ○⟪ (sels2 ++ [ HD ]) ⟫ⁿ
        ≡⟨ ∘⟪⟫ⁿ∘++
             (replaceAt sels1 (⟪ [] ⟫ⁿ)
                        (⟪ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels1 ++ [ TL ] ⟫ⁿ))
             sels2 [ HD ] ⟩
      (replaceAt sels1 ⟪ [] ⟫ⁿ
                 (⟪ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ (sels1 ++ [ TL ]) ⟫ⁿ))
                   ○⟪ [ HD ] ⟫ⁿ ○⟪ sels2 ⟫ⁿ
        ≡⟨ cong (flip _○⟪_⟫ⁿ sels2)
                (sym $ setConsAtPreservesEval′ sels1 [ HD ]) ⟩
      replaceAt sels1 ⟪ [ HD ] ⟫ⁿ
                (⟪ [ HD ] ++ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ
                  ⟪ [ HD ] ++ sels1 ++ [ TL ] ⟫ⁿ) ○⟪ sels2 ⟫ⁿ
          
          
      ∎

setConsAtPreservesEval′ (TL ∷ sels1) sels2
  rewrite sym $ LM.assoc sels2 [ TL ] (sels1 ++ [ TL ])
        | sym $ LM.assoc sels2 [ TL ] (sels1 ++ [ HD ])
        | setConsAtPreservesEval′ sels1 (sels2 ++ [ TL ])
        | setConsAtPreservesEval′ sels1 [ TL ]
        | ∘⟪⟫ⁿ∘++
             (replaceAt sels1 ⟪ [] ⟫ⁿ
               (⟪ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels1 ++ [ TL ] ⟫ⁿ))
             sels2 (TL ∷ [])

  = refl

-- setNilAtPreservesEval′′

setNilAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  ⟦⌈ setNilAt (sels1 ++ sels2) ⌉⟧ v !! sels1
    ≡ ⟦⌈ setNilAt sels2 ⌉⟧ (v !! sels1)

setNilAtPreservesEval′′ v sels1 sels2 = begin
  (⟦⌈ setNilAt (sels1 ++ sels2) ⌉⟧ v) !! sels1
    ≡⟨ refl ⟩
  (⟦⌈ (replaceAt (sels1 ++ sels2) ⟪ [] ⟫ⁿ []ⁿ) ⌉⟧ v) !! sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘!!ⁿ
               (replaceAt (sels1 ++ sels2) ⟪ [] ⟫ⁿ []ⁿ) sels1 v ⟩
  ⟦⌈ replaceAt (sels1 ++ sels2) ⟪ [] ⟫ⁿ []ⁿ !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip _!!ⁿ_ sels1)
                  (replaceAt∘++ sels1 sels2 (⟪ [] ⟫ⁿ) []ⁿ)) ⟩
  ⟦⌈ replaceAt sels1 ⟪ [] ⟫ⁿ
               (replaceAt sels2 (⟪ [] ⟫ⁿ !!ⁿ sels1) []ⁿ) !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (!!ⁿ∘replaceAt sels1 ⟪ [] ⟫ⁿ
              (replaceAt sels2 (⟪ [] ⟫ⁿ !!ⁿ sels1) []ⁿ)) ⟩
  ⟦⌈ replaceAt sels2 (⟪ [] ⟫ⁿ !!ⁿ sels1) []ⁿ ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip (replaceAt sels2) []ⁿ)
                  (!!ⁿ∘⟪⟫ⁿ [] sels1)) ⟩
  ⟦⌈ replaceAt sels2 ⟪ sels1 ⟫ⁿ []ⁿ ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v) (setNilAtPreservesEval′ sels2 sels1) ⟩
  ⟦⌈ replaceAt sels2 ⟪ [] ⟫ⁿ []ⁿ ○⟪ sels1 ⟫ⁿ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○⟪⟫ⁿ (replaceAt sels2 ⟪ [] ⟫ⁿ []ⁿ) sels1 v ⟩
  ⟦⌈ replaceAt sels2 ⟪ [] ⟫ⁿ []ⁿ ⌉⟧ (v !! sels1)
    ≡⟨ refl ⟩
  ⟦⌈ setNilAt sels2 ⌉⟧ (v !! sels1)
  ∎

-- setConsAtPreservesEval′′

setConsAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  ⟦⌈ setConsAt (sels1 ++ sels2) ⌉⟧ v !! sels1
    ≡ ⟦⌈ setConsAt sels2 ⌉⟧ (v !! sels1)

setConsAtPreservesEval′′ v sels1 sels2 = begin
  ⟦⌈ setConsAt (sels1 ++ sels2) ⌉⟧ v !! sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘!!ⁿ (setConsAt (sels1 ++ sels2)) sels1 v ⟩
  ⟦⌈ setConsAt (sels1 ++ sels2) !!ⁿ sels1 ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ replaceAt (sels1 ++ sels2) ⟪ [] ⟫ⁿ
               (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                  ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ) !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip _!!ⁿ_ sels1)
                  (replaceAt∘++ sels1 sels2 (⟪ [] ⟫ⁿ)
                    (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                      ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ))) ⟩
  ⟦⌈ replaceAt sels1 ⟪ [] ⟫ⁿ
               (replaceAt sels2 (⟪ [] ⟫ⁿ !!ⁿ sels1)
                          (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                            ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ)) !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (!!ⁿ∘replaceAt sels1 (⟪ [] ⟫ⁿ)
              (replaceAt sels2 (⟪ [] ⟫ⁿ !!ⁿ sels1)
                         (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                           ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ))) ⟩
  ⟦⌈ replaceAt sels2 (⟪ [] ⟫ⁿ !!ⁿ sels1)
            (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
              ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip (replaceAt sels2)
                        (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                          ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ))
                  (!!ⁿ∘⟪⟫ⁿ [] sels1)) ⟩
  ⟦⌈ replaceAt sels2 ⟪ sels1 ⟫ⁿ
                     (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                       ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (replaceAt sels2 (⟪ sels1 ⟫ⁿ))
                  (cong (flip _∷ⁿ_ (⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ))
                        (cong ⟪_⟫ⁿ (LM.assoc sels1 sels2 [ HD ])))) ⟩
  ⟦⌈ replaceAt sels2 ⟪ sels1 ⟫ⁿ
                     (⟪ sels1 ++ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ
                       ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (replaceAt sels2 ⟪ sels1 ⟫ⁿ)
                  (cong (_∷ⁿ_ (⟪ sels1 ++ sels2 ++ [ HD ] ⟫ⁿ))
                        (cong ⟪_⟫ⁿ (LM.assoc sels1 sels2 [ TL ])))) ⟩
  ⟦⌈ replaceAt sels2 ⟪ sels1 ⟫ⁿ
               (⟪ sels1 ++ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ
                  ⟪ sels1 ++ sels2 ++ [ TL ] ⟫ⁿ) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v) (setConsAtPreservesEval′ sels2 sels1) ⟩
  ⟦⌈ replaceAt sels2 ⟪ [] ⟫ⁿ
               (⟪ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ) ○⟪ sels1 ⟫ⁿ ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ setConsAt sels2 ○⟪ sels1 ⟫ⁿ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○⟪⟫ⁿ (setConsAt sels2) sels1 v ⟩
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
    ⟦⌈ replaceAt sels ⟪ [ HD ] ⟫ⁿ []ⁿ ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ HD ] []ⁿ) ⟩
    ⟦⌈ replaceAt ([ HD ] ++ sels) ⟪ [] ⟫ⁿ []ⁿ !!ⁿ [ HD ] ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ HD ] ++ sels) ⟪ [] ⟫ⁿ []ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ HD ]
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
    ⟦⌈ replaceAt sels ⟪ [ TL ] ⟫ⁿ []ⁿ ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ TL ] []ⁿ) ⟩
    ⟦⌈ replaceAt ([ TL ] ++ sels) ⟪ [] ⟫ⁿ []ⁿ !!ⁿ [ TL ] ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ TL ] ++ sels) ⟪ [] ⟫ⁿ []ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ TL ]
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
    ⟦⌈ replaceAt sels ⟪ [ HD ] ⟫ⁿ
                      (⟪ (HD ∷ sels) ++ [ HD ] ⟫ⁿ ∷ⁿ
                        ⟪ (HD ∷ sels) ++ [ TL ] ⟫ⁿ) ⌉⟧
      (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ HD ]
                                 (⟪ HD ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ
                                   ⟪ HD ∷ sels ++ [ TL ] ⟫ⁿ)) ⟩
    ⟦⌈ replaceAt ([ HD ] ++ sels) ⟪ [] ⟫ⁿ
                 (⟪ HD ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ HD ∷ sels ++ [ TL ] ⟫ⁿ) !!ⁿ
                   [ HD ] ⌉⟧
       (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ HD ] ++ sels) ⟪ [] ⟫ⁿ
                 (⟪ HD ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ HD ∷ sels ++ [ TL ] ⟫ⁿ) ⌉⟧
                     (v1 ∷ˣ v2) !! [ HD ]
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
    ⟦⌈ replaceAt sels ⟪ [ TL ] ⟫ⁿ
                 (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ) ⌉⟧
           (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              (replaceAt∘⟪⟫ⁿ sels [ TL ]
                             (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ
                               ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ)) ⟩
    ⟦⌈ replaceAt ([ TL ] ++ sels) (⟪ [] ⟫ⁿ)
                 (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ)
                   !!ⁿ [ TL ] ⌉⟧
           (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ replaceAt ([ TL ] ++ sels) ⟪ [] ⟫ⁿ
                 (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ) ⌉⟧
                 (v1 ∷ˣ v2)
                   !! [ TL ]
      ≡⟨ refl ⟩
    ⟦⌈ setConsAt ([ TL ] ++ sels) ⌉⟧ (v1 ∷ˣ v2) !! [ TL ]
      ≡⟨ setConsAtPreservesEval′′ (v1 ∷ˣ v2) [ TL ] sels ⟩
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
    ⟦⌈ IfNilⁿ sels (nt1 ○ setNilAt sels)
                   (nt2 ○ (setConsAt sels)) ⌉⟧ v
  ≡
  ⟦⌈ IfNilⁿ sels nt1 nt2 ⌉⟧ v

condPropagatorsPreserveEval sels nt1 nt2 v
  rewrite ⟦⟧∘⟪⟫ sels v
  with v !! sels | inspect (_!!_ v) sels 

... | []ˣ | [ ≡[]ˣ ]ⁱ = begin
  ⟦⌈ nt1 ○ setNilAt sels ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○ nt1 (setNilAt sels) v ⟩
  ⟦⌈ nt1 ⌉⟧ (⟦⌈ setNilAt sels ⌉⟧ v)
    ≡⟨ cong ⟦⌈ nt1 ⌉⟧ (⟦⌈⌉⟧∘setNilAt sels v ≡[]ˣ) ⟩
  ⟦⌈ nt1 ⌉⟧ v
  ∎

... | _ ∷ˣ _ | [ ≡∷ˣ ]ⁱ = begin
  ⟦⌈ nt2 ○ setConsAt sels ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○ nt2 (setConsAt sels) v ⟩
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

⟦⌈⌉⟧∘propagateIfCond ⟪ sels ⟫ⁿ v = refl

⟦⌈⌉⟧∘propagateIfCond (IfNilⁿ sels nt1 nt2) v = begin
  ⟦⌈ propagateIfCond (IfNilⁿ sels nt1 nt2) ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ IfNilⁿ sels (propagateIfCond nt1 ○ setNilAt sels)
                 (propagateIfCond nt2 ○ setConsAt sels) ⌉⟧ v
    ≡⟨ refl ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ propagateIfCond nt1 ○ setNilAt sels ⌉⟧ v)
        (⟦⌈ propagateIfCond nt2 ○ setConsAt sels ⌉⟧ v)
    ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
             (⟦⌈⌉⟧∘○ (propagateIfCond nt1) (setNilAt sels) v)
             (⟦⌈⌉⟧∘○ (propagateIfCond nt2) (setConsAt sels) v) ⟩
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
             (sym $ ⟦⌈⌉⟧∘○ nt1 (setNilAt sels) v)
             (sym $ ⟦⌈⌉⟧∘○ nt2 (setConsAt sels) v) ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ nt1 ○ setNilAt sels ⌉⟧ v)
        (⟦⌈ nt2 ○ setConsAt sels ⌉⟧ v)
    ≡⟨ refl ⟩
  ⟦⌈ IfNilⁿ sels (nt1 ○ setNilAt sels)
                 (nt2 ○ setConsAt sels) ⌉⟧ v
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
norm t = propagateIfCond ⌋ t ⌊

-- ⟦⌈⌉⟧∘norm

⟦⌈⌉⟧∘norm : ∀ t v → ⟦⌈ norm t ⌉⟧ v ≡ ⟦ t ⟧ v

⟦⌈⌉⟧∘norm t v = begin
  ⟦⌈ norm t ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ propagateIfCond ⌋ t ⌊ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘propagateIfCond ⌋ t ⌊ v ⟩
  ⟦⌈ ⌋ t ⌊ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘⌋⌊ t v ⟩
  ⟦ t ⟧ v
  ∎

--
