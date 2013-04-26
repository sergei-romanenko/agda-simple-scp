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
  replaceAt sels (NSelCmp []) NNil

-- setConsAt

setConsAt : (sels : List Selector) → NTrm

setConsAt sels = 
  replaceAt sels (NSelCmp []) 
    (NSelCmp (sels ++ [ HD ]) ∷ⁿ NSelCmp (sels ++ [ TL ]))


-- propagateIfCond

propagateIfCond : (nt : NTrm) → NTrm

propagateIfCond NNil = NNil
propagateIfCond (nt1 ∷ⁿ nt2) =
  propagateIfCond nt1 ∷ⁿ propagateIfCond nt2
propagateIfCond (NSelCmp sels) = NSelCmp sels
propagateIfCond (NIfNil sels nt1 nt2) =
  NIfNil sels
    (normNCmp (propagateIfCond nt1) (setNilAt sels))
    (normNCmp (propagateIfCond nt2) (setConsAt sels))
propagateIfCond NBottom = NBottom

-- Establishing the correctness of `propagateIfCond` is once again decomposed
-- into a sequence of lemmas. 

-- setNilAtPreservesEval′

setNilAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 (NSelCmp sels2) NNil
    ≡ normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) sels2

setNilAtPreservesEval′ [] sels2 = refl

setNilAtPreservesEval′ (HD ∷ sels1) sels2 =
  begin
    replaceAt (HD ∷ sels1) (NSelCmp sels2) NNil
      ≡⟨ refl ⟩
    replaceAt sels1 (NSelCmp (sels2 ++ [ HD ])) NNil ∷ⁿ
      NSelCmp (sels2 ++ [ TL ])
      ≡⟨ cong (flip _∷ⁿ_ (NSelCmp (sels2 ++ [ TL ])))
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ HD ])) ⟩
    normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) (sels2 ++ [ HD ]) ∷ⁿ
      NSelCmp (sels2 ++ [ TL ])
      ≡⟨ cong (flip _∷ⁿ_ (NSelCmp (sels2 ++ [ TL ])))
              (normNCmpSels∘++ (replaceAt sels1 (NSelCmp []) NNil)
                               sels2 [ HD ]) ⟩
    normNCmpSels
      (normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) [ HD ]) sels2 ∷ⁿ
        (NSelCmp (sels2 ++ [ TL ]))
      ≡⟨ cong (flip _∷ⁿ_ (NSelCmp (sels2 ++ [ TL ])))
              (cong (flip normNCmpSels sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ HD ])) ⟩
    normNCmpSels (replaceAt sels1 (NSelCmp [ HD ]) NNil) sels2 ∷ⁿ
      NSelCmp (sels2 ++ [ TL ])
      ≡⟨ refl ⟩
    normNCmpSels (replaceAt (HD ∷ sels1) (NSelCmp []) NNil) sels2
  ∎

setNilAtPreservesEval′ (TL ∷ sels1) sels2 =
  begin
    replaceAt (TL ∷ sels1) (NSelCmp sels2) NNil
      ≡⟨ refl ⟩
    NSelCmp (sels2 ++ [ HD ]) ∷ⁿ
      replaceAt sels1 (NSelCmp (sels2 ++ [ TL ])) NNil
      ≡⟨ cong (_∷ⁿ_ (NSelCmp (sels2 ++ [ HD ])))
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ TL ])) ⟩
    NSelCmp (sels2 ++ [ HD ]) ∷ⁿ
      normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) (sels2 ++ [ TL ])
      ≡⟨ cong (_∷ⁿ_ (NSelCmp (sels2 ++ [ HD ])))
              (normNCmpSels∘++ (replaceAt sels1 (NSelCmp []) NNil)
                               sels2 (TL ∷ [])) ⟩
    NSelCmp (sels2 ++ [ HD ]) ∷ⁿ
      normNCmpSels
            (normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) [ TL ]) sels2
      ≡⟨ cong (_∷ⁿ_ (NSelCmp (sels2 ++ [ HD ])))
              (cong (flip normNCmpSels sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ TL ])) ⟩
    NSelCmp (sels2 ++ [ HD ]) ∷ⁿ
      normNCmpSels (replaceAt sels1 (NSelCmp [ TL ]) NNil) sels2
      ≡⟨ refl ⟩
    normNCmpSels (replaceAt (TL ∷ sels1) (NSelCmp []) NNil) sels2
  ∎

-- setConsAtPreservesEval′

setConsAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 (NSelCmp sels2)
            (NSelCmp (sels2 ++ sels1 ++ [ HD ]) ∷ⁿ
              NSelCmp (sels2 ++ sels1 ++ [ TL ]))
  ≡
  normNCmpSels (replaceAt sels1 (NSelCmp [])
                          (NSelCmp (sels1 ++ [ HD ]) ∷ⁿ
                            NSelCmp (sels1 ++ [ TL ])))
               sels2

setConsAtPreservesEval′ [] sels2 = refl

setConsAtPreservesEval′ (HD ∷ sels1) sels2
  rewrite sym $ ++-assoc sels2 [ HD ] (sels1 ++ [ HD ])
        | sym $ ++-assoc sels2 [ HD ] (sels1 ++ [ TL ])
  = cong (flip _∷ⁿ_ (NSelCmp (sels2 ++ [ TL ])))
         helper
  where
    helper = begin
      replaceAt sels1 (NSelCmp (sels2 ++ [ HD ]))
          (NSelCmp ((sels2 ++ [ HD ]) ++ sels1 ++ [ HD ]) ∷ⁿ
            NSelCmp ((sels2 ++ [ HD ]) ++ sels1 ++ [ TL ]))
        ≡⟨ setConsAtPreservesEval′ sels1 (sels2 ++ [ HD ]) ⟩
      normNCmpSels
          (replaceAt sels1 (NSelCmp [])
              (NSelCmp (sels1 ++ [ HD ]) ∷ⁿ NSelCmp (sels1 ++ [ TL ])))
          (sels2 ++ [ HD ])
        ≡⟨ normNCmpSels∘++
             (replaceAt sels1 (NSelCmp [])
               (NSelCmp (sels1 ++ [ HD ]) ∷ⁿ NSelCmp (sels1 ++ [ TL ])))
             sels2 (HD ∷ []) ⟩
      normNCmpSels
        (normNCmpSels
          (replaceAt sels1 (NSelCmp [])
                     (NSelCmp (sels1 ++ [ HD ]) ∷ⁿ NSelCmp (sels1 ++ [ TL ])))
          (HD ∷ []))
        sels2
        ≡⟨ cong (flip normNCmpSels sels2)
                (sym $ setConsAtPreservesEval′ sels1 [ HD ]) ⟩
      normNCmpSels
          (replaceAt sels1 (NSelCmp [ HD ])
            ((NSelCmp ([ HD ] ++ sels1 ++ [ HD ])) ∷ⁿ
              NSelCmp ([ HD ] ++ sels1 ++ [ TL ])))
          sels2
      ∎

setConsAtPreservesEval′ (TL ∷ sels1) sels2
  rewrite sym $ ++-assoc sels2 [ TL ] (sels1 ++ [ TL ])
        | sym $ ++-assoc sels2 [ TL ] (sels1 ++ [ HD ])
        | setConsAtPreservesEval′ sels1 (sels2 ++ [ TL ])
        | setConsAtPreservesEval′ sels1 [ TL ]
        | normNCmpSels∘++
             (replaceAt sels1 (NSelCmp [])
               (NSelCmp (sels1 ++ [ HD ]) ∷ⁿ NSelCmp (sels1 ++ [ TL ])))
             sels2 (TL ∷ [])

  = refl

-- setNilAtPreservesEval′′

setNilAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  evalSels (⟦⌈_⌉⟧ (setNilAt (sels1 ++ sels2)) v) sels1
    ≡ ⟦⌈_⌉⟧ (setNilAt sels2) (evalSels v sels1)

setNilAtPreservesEval′′ v sels1 sels2 = begin
  evalSels (⟦⌈_⌉⟧ (setNilAt (sels1 ++ sels2)) v) sels1
    ≡⟨ refl ⟩
  evalSels (⟦⌈_⌉⟧ (replaceAt (sels1 ++ sels2) (NSelCmp []) NNil) v) sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘normSelsNCmp
               (replaceAt (sels1 ++ sels2) (NSelCmp []) NNil) sels1 v ⟩
  ⟦⌈_⌉⟧ (normSelsNCmp (replaceAt (sels1 ++ sels2) (NSelCmp []) NNil) sels1) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip normSelsNCmp sels1)
                  (replaceAt∘++ sels1 sels2 (NSelCmp []) NNil)) ⟩
  ⟦⌈_⌉⟧ (normSelsNCmp (replaceAt sels1 (NSelCmp [])
                       (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil))
                       sels1) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (normSelsNCmp∘replaceAt sels1 (NSelCmp [])
              (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil)) ⟩
  ⟦⌈_⌉⟧ (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip (replaceAt sels2) NNil)
                  (normSelsNCmp∘NSelCmp [] sels1)) ⟩
  ⟦⌈_⌉⟧ (replaceAt sels2 (NSelCmp sels1) NNil) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v) (setNilAtPreservesEval′ sels2 sels1) ⟩
  ⟦⌈_⌉⟧ (normNCmpSels (replaceAt sels2 (NSelCmp []) NNil) sels1) v
    ≡⟨ ⟦⌈⌉⟧∘normNCmpSels (replaceAt sels2 (NSelCmp []) NNil) sels1 v ⟩
  ⟦⌈_⌉⟧ (replaceAt sels2 (NSelCmp []) NNil) (evalSels v sels1)
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (setNilAt sels2) (evalSels v sels1)
  ∎

-- setConsAtPreservesEval′′

setConsAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  evalSels (⟦⌈_⌉⟧ (setConsAt (sels1 ++ sels2)) v) sels1
    ≡ ⟦⌈_⌉⟧ (setConsAt sels2) (evalSels v sels1)

setConsAtPreservesEval′′ v sels1 sels2 = begin
  evalSels (⟦⌈_⌉⟧ (setConsAt (sels1 ++ sels2)) v) sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘normSelsNCmp (setConsAt (sels1 ++ sels2)) sels1 v ⟩
  ⟦⌈_⌉⟧ (normSelsNCmp (setConsAt (sels1 ++ sels2)) sels1) v
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (normSelsNCmp (replaceAt (sels1 ++ sels2) (NSelCmp [])
                          (NSelCmp ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                            NSelCmp ((sels1 ++ sels2) ++ [ TL ])))
                       sels1) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip normSelsNCmp sels1)
                  (replaceAt∘++ sels1 sels2 (NSelCmp [])
                    (NSelCmp ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                      NSelCmp ((sels1 ++ sels2) ++ [ TL ])))) ⟩
  ⟦⌈_⌉⟧ (normSelsNCmp
           (replaceAt sels1 (NSelCmp [])
             (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1)
                        (NSelCmp ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                          NSelCmp ((sels1 ++ sels2) ++ [ TL ]))))
           sels1) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (normSelsNCmp∘replaceAt sels1 (NSelCmp [])
              (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1)
                         (NSelCmp ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                           NSelCmp ((sels1 ++ sels2) ++ [ TL ])))) ⟩
  ⟦⌈_⌉⟧ (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1)
            (NSelCmp ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
              NSelCmp ((sels1 ++ sels2) ++ [ TL ]))) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip (replaceAt sels2)
                        (NSelCmp ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                          NSelCmp ((sels1 ++ sels2) ++ [ TL ])))
                  (normSelsNCmp∘NSelCmp [] sels1)) ⟩
  ⟦⌈_⌉⟧ (replaceAt sels2
                    (NSelCmp sels1)
                    (NSelCmp ((sels1 ++ sels2) ++ [ HD ]) ∷ⁿ
                      NSelCmp ((sels1 ++ sels2) ++ [ TL ]))) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (replaceAt sels2 (NSelCmp sels1))
                  (cong (flip _∷ⁿ_ (NSelCmp ((sels1 ++ sels2) ++ [ TL ])))
                        (cong NSelCmp (++-assoc sels1 sels2 [ HD ])))) ⟩
  ⟦⌈_⌉⟧ (replaceAt sels2
                    (NSelCmp sels1)
                    (NSelCmp (sels1 ++ sels2 ++ [ HD ]) ∷ⁿ
                      NSelCmp ((sels1 ++ sels2) ++ [ TL ]))) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (replaceAt sels2 (NSelCmp sels1))
                  (cong (_∷ⁿ_ (NSelCmp (sels1 ++ sels2 ++ [ HD ])))
                        (cong NSelCmp (++-assoc sels1 sels2 [ TL ])))) ⟩
  ⟦⌈_⌉⟧ (replaceAt sels2
                    (NSelCmp sels1)
                    (NSelCmp (sels1 ++ sels2 ++ [ HD ]) ∷ⁿ
                      NSelCmp (sels1 ++ sels2 ++ [ TL ]))) v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (setConsAtPreservesEval′ sels2 sels1) ⟩
  ⟦⌈_⌉⟧ (normNCmpSels
            (replaceAt sels2 (NSelCmp [])
                       (NSelCmp (sels2 ++ [ HD ]) ∷ⁿ
                         NSelCmp (sels2 ++ [ TL ])))
            sels1) v
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (normNCmpSels (setConsAt sels2) sels1) v
    ≡⟨ ⟦⌈⌉⟧∘normNCmpSels (setConsAt sels2) sels1 v ⟩
  ⟦⌈_⌉⟧ (setConsAt sels2) (evalSels v sels1)
  ∎

-- Auxiliaries

VBottom≢VNil : VBottom ≢ VNil
VBottom≢VNil = λ ()

VCons≢VNil : ∀ {v1 v2} → VCons v1 v2 ≢ VNil
VCons≢VNil = λ ()

VCons≢VBottom : ∀ {v1 v2} → VCons v1 v2 ≢ VBottom
VCons≢VBottom = λ ()

-- ⟦⌈⌉⟧∘setNilAt

⟦⌈⌉⟧∘setNilAt : (sels : List Selector) (v : Val) →
  evalSels v sels ≡ VNil → ⟦⌈_⌉⟧ (setNilAt sels) v ≡ v

⟦⌈⌉⟧∘setNilAt [] VNil h = refl

⟦⌈⌉⟧∘setNilAt (sel ∷ sels) VNil h
  rewrite evalSels-VBottom sels
  = ⊥-elim (VBottom≢VNil h)

⟦⌈⌉⟧∘setNilAt [] (VCons v1 v2) h =
  ⊥-elim (VCons≢VNil h)

⟦⌈⌉⟧∘setNilAt (HD ∷ sels) (VCons v1 v2) h =
  cong (flip VCons v2) helper
  where
  helper = begin
    ⟦⌈_⌉⟧ (replaceAt sels (NSelCmp [ HD ]) NNil) (VCons v1 v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ HD ] NNil) ⟩
    ⟦⌈_⌉⟧ (normSelsNCmp (replaceAt ([ HD ] ++ sels) (NSelCmp []) NNil) [ HD ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (replaceAt ([ HD ] ++ sels) (NSelCmp []) NNil)
                     (VCons v1 v2)) [ HD ]
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (setNilAt ([ HD ] ++ sels)) (VCons v1 v2)) [ HD ]
      ≡⟨ setNilAtPreservesEval′′ (VCons v1 v2) [ HD ] sels ⟩
    ⟦⌈_⌉⟧ (setNilAt sels) (evalSels (VCons v1 v2) [ HD ])
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (setNilAt sels) v1
      ≡⟨ ⟦⌈⌉⟧∘setNilAt sels v1 h ⟩
    v1
    ∎

⟦⌈⌉⟧∘setNilAt (TL ∷ sels) (VCons v1 v2) h =
  cong (VCons v1) helper
  where
  helper = begin
    ⟦⌈_⌉⟧ (replaceAt sels (NSelCmp [ TL ]) NNil) (VCons v1 v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ TL ] NNil) ⟩
    ⟦⌈_⌉⟧ (normSelsNCmp (replaceAt ([ TL ] ++ sels) (NSelCmp []) NNil) [ TL ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (replaceAt ([ TL ] ++ sels) (NSelCmp []) NNil)
                     (VCons v1 v2)) [ TL ]
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (setNilAt ([ TL ] ++ sels)) (VCons v1 v2)) [ TL ]
      ≡⟨ setNilAtPreservesEval′′ (VCons v1 v2) [ TL ] sels ⟩
    ⟦⌈_⌉⟧ (setNilAt sels) (evalSels (VCons v1 v2) [ TL ])
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (setNilAt sels) v2
      ≡⟨ ⟦⌈⌉⟧∘setNilAt sels v2 h ⟩
    v2
    ∎

⟦⌈⌉⟧∘setNilAt sels VBottom h
  rewrite evalSels-VBottom sels
  = ⊥-elim (VBottom≢VNil h)

-- ⟦⌈⌉⟧∘setConsAt

⟦⌈⌉⟧∘setConsAt : (sels : List Selector) (v u1 u2 : Val) →
  evalSels v sels ≡ VCons u1 u2 → ⟦⌈_⌉⟧ (setConsAt sels) v ≡ v

⟦⌈⌉⟧∘setConsAt [] VNil u1 u2 h = ⊥-elim (VCons≢VNil (sym h))

⟦⌈⌉⟧∘setConsAt (sel ∷ sels) VNil u1 u2 h
  rewrite evalSels-VBottom sels
  = ⊥-elim (VCons≢VBottom (sym h))

⟦⌈⌉⟧∘setConsAt [] (VCons v1 v2) u1 u2 h = refl

⟦⌈⌉⟧∘setConsAt (HD ∷ sels) (VCons v1 v2) u1 u2 h =
  cong (flip VCons v2) helper
  where
  helper = begin
    ⟦⌈_⌉⟧ (replaceAt sels (NSelCmp [ HD ])
                      (NSelCmp ((HD ∷ sels) ++ [ HD ]) ∷ⁿ
                        NSelCmp ((HD ∷ sels) ++ [ TL ])))
      (VCons v1 v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ HD ]
                                 (NSelCmp (HD ∷ sels ++ [ HD ]) ∷ⁿ
                                   NSelCmp (HD ∷ sels ++ [ TL ]))) ⟩
    ⟦⌈_⌉⟧ (normSelsNCmp (replaceAt ([ HD ] ++ sels) (NSelCmp [])
                                    (NSelCmp (HD ∷ sels ++ [ HD ]) ∷ⁿ
                                      NSelCmp (HD ∷ sels ++ [ TL ])))
                         [ HD ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (replaceAt ([ HD ] ++ sels) (NSelCmp [])
                                (NSelCmp (HD ∷ sels ++ [ HD ]) ∷ⁿ
                                  NSelCmp (HD ∷ sels ++ [ TL ])))
                     (VCons v1 v2))
             [ HD ]
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (setConsAt ([ HD ] ++ sels)) (VCons v1 v2)) [ HD ]
      ≡⟨ setConsAtPreservesEval′′ (VCons v1 v2) (HD ∷ []) sels ⟩
    ⟦⌈_⌉⟧ (setConsAt sels) (evalSels v1 [])
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (setConsAt sels) v1
      ≡⟨ ⟦⌈⌉⟧∘setConsAt sels v1 u1 u2 h ⟩
    v1
    ∎

⟦⌈⌉⟧∘setConsAt (TL ∷ sels) (VCons v1 v2) v3 v4 h =
  cong (VCons v1) helper
  where
  helper = begin
    ⟦⌈_⌉⟧ ((replaceAt sels (NSelCmp (TL ∷ []))
                       (NSelCmp (TL ∷ sels ++ [ HD ]) ∷ⁿ
                         NSelCmp (TL ∷ sels ++ [ TL ]))))
           (VCons v1 v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ TL ]
                                 (NSelCmp (TL ∷ sels ++ [ HD ]) ∷ⁿ
                                   NSelCmp (TL ∷ sels ++ [ TL ]))) ⟩
    ⟦⌈_⌉⟧ (normSelsNCmp (replaceAt ([ TL ] ++ sels) (NSelCmp [])
                                    (NSelCmp (TL ∷ sels ++ [ HD ]) ∷ⁿ
                                      NSelCmp (TL ∷ sels ++ [ TL ])))
                         [ TL ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (replaceAt ([ TL ] ++ sels) (NSelCmp [])
                                (NSelCmp (TL ∷ sels ++ [ HD ]) ∷ⁿ
                                  NSelCmp (TL ∷ sels ++ [ TL ])))
                     (VCons v1 v2))
             [ TL ]
      ≡⟨ refl ⟩
    evalSels (⟦⌈_⌉⟧ (setConsAt ([ TL ] ++ sels)) (VCons v1 v2)) [ TL ]
      ≡⟨ setConsAtPreservesEval′′ (VCons v1 v2) (TL ∷ []) sels ⟩
    ⟦⌈_⌉⟧ (setConsAt sels) (evalSels v2 [])
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (setConsAt sels) v2
      ≡⟨ ⟦⌈⌉⟧∘setConsAt sels v2 v3 v4 h ⟩
    v2
    ∎

⟦⌈⌉⟧∘setConsAt sels VBottom v1 v2 h
  rewrite  evalSels-VBottom sels
  = ⊥-elim (VCons≢VBottom (sym h))

-- condPropagatorsPreserveEval

condPropagatorsPreserveEval :
  (sels : List Selector) (nt1 nt2 : NTrm) (v : Val) →
    ⟦⌈_⌉⟧ (NIfNil sels (normNCmp nt1 (setNilAt sels))
                        (normNCmp nt2 (setConsAt sels))) v
  ≡
  ⟦⌈_⌉⟧ (NIfNil sels nt1 nt2) v

condPropagatorsPreserveEval sels nt1 nt2 v
  rewrite ⟦⟧∘sels2trm sels v
  with evalSels v sels | inspect (evalSels v) sels 

... | VNil | [ ≡VNil ]ⁱ = begin
  ⟦⌈_⌉⟧ (normNCmp nt1 (setNilAt sels)) v
    ≡⟨ ⟦⌈⌉⟧∘normNCmp nt1 (setNilAt sels) v ⟩
  ⟦⌈_⌉⟧ nt1 (⟦⌈_⌉⟧ (setNilAt sels) v)
    ≡⟨ cong (⟦⌈_⌉⟧ nt1) (⟦⌈⌉⟧∘setNilAt sels v ≡VNil) ⟩
  ⟦⌈_⌉⟧ nt1 v
  ∎

... | VCons _ _ | [ ≡VCons ]ⁱ = begin
  ⟦⌈_⌉⟧ (normNCmp nt2 (setConsAt sels)) v
    ≡⟨ ⟦⌈⌉⟧∘normNCmp nt2 (setConsAt sels) v ⟩
  ⟦⌈_⌉⟧ nt2 (⟦⌈_⌉⟧ (setConsAt sels) v)
    ≡⟨ cong (⟦⌈_⌉⟧ nt2) (⟦⌈⌉⟧∘setConsAt sels v _ _ ≡VCons) ⟩
  ⟦_⟧ ⌈ nt2 ⌉ v   
  ∎

... | VBottom | _ = refl

--
-- ⟦⌈⌉⟧∘propagateIfCond
--

⟦⌈⌉⟧∘propagateIfCond : (nt : NTrm) (v : Val) →
  ⟦⌈_⌉⟧ (propagateIfCond nt) v ≡ ⟦⌈_⌉⟧ nt v

⟦⌈⌉⟧∘propagateIfCond NNil v = refl

⟦⌈⌉⟧∘propagateIfCond (nt1 ∷ⁿ nt2) v
  rewrite ⟦⌈⌉⟧∘propagateIfCond nt1 v
        | ⟦⌈⌉⟧∘propagateIfCond nt2 v
 = refl

⟦⌈⌉⟧∘propagateIfCond (NSelCmp sels) v = refl

⟦⌈⌉⟧∘propagateIfCond (NIfNil sels nt1 nt2) v = begin
  ⟦⌈_⌉⟧ (propagateIfCond (NIfNil sels nt1 nt2)) v
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (NIfNil sels (normNCmp (propagateIfCond nt1) (setNilAt sels))
                      (normNCmp (propagateIfCond nt2) (setConsAt sels))) v
    ≡⟨ refl ⟩
  ifNil (⟦_⟧ (sels2trm sels) v)
        (⟦⌈_⌉⟧ (normNCmp (propagateIfCond nt1) (setNilAt sels)) v)
        (⟦⌈_⌉⟧ (normNCmp (propagateIfCond nt2) (setConsAt sels)) v)
    ≡⟨ cong₂ (ifNil (⟦_⟧ (sels2trm sels) v))
             (⟦⌈⌉⟧∘normNCmp (propagateIfCond nt1) (setNilAt sels) v)
             (⟦⌈⌉⟧∘normNCmp (propagateIfCond nt2) (setConsAt sels) v) ⟩
  ifNil (⟦_⟧ (sels2trm sels) v)
        (⟦⌈_⌉⟧ (propagateIfCond nt1) (⟦⌈_⌉⟧ (setNilAt sels) v))
        (⟦⌈_⌉⟧ (propagateIfCond nt2) (⟦⌈_⌉⟧ (setConsAt sels) v))
    ≡⟨ cong₂ (ifNil (⟦_⟧ (sels2trm sels) v))
             (⟦⌈⌉⟧∘propagateIfCond nt1 (⟦⌈_⌉⟧ (setNilAt sels) v))
             (⟦⌈⌉⟧∘propagateIfCond nt2 (⟦⌈_⌉⟧ (setConsAt sels) v)) ⟩
  ifNil (⟦_⟧ (sels2trm sels) v)
        (⟦⌈_⌉⟧ nt1 (⟦⌈_⌉⟧ (setNilAt sels) v))
        (⟦⌈_⌉⟧ nt2 (⟦⌈_⌉⟧ (setConsAt sels) v))
    ≡⟨ cong₂ (ifNil (⟦_⟧ (sels2trm sels) v))
             (sym $ ⟦⌈⌉⟧∘normNCmp nt1 (setNilAt sels) v)
             (sym $ ⟦⌈⌉⟧∘normNCmp nt2 (setConsAt sels) v) ⟩
  ifNil (⟦_⟧ (sels2trm sels) v)
        (⟦⌈_⌉⟧ (normNCmp nt1 (setNilAt sels)) v)
        (⟦⌈_⌉⟧ (normNCmp nt2 (setConsAt sels)) v)
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (NIfNil sels (normNCmp nt1 (setNilAt sels))
                      (normNCmp nt2 (setConsAt sels))) v
    ≡⟨ condPropagatorsPreserveEval sels nt1 nt2 v ⟩
  ⟦⌈_⌉⟧ (NIfNil sels nt1 nt2) v
  ∎

⟦⌈⌉⟧∘propagateIfCond NBottom v = refl

--
-- norm
--

-- We can combine the first two stages - normalization and
-- positive information propagation - into a single function,
-- and trivially establish its correctness.

norm : (t : Trm) → NTrm
norm t = propagateIfCond (normConv t)

-- ⟦⌈⌉⟧∘norm

⟦⌈⌉⟧∘norm : ∀ t v → ⟦⌈_⌉⟧ (norm t) v ≡ ⟦_⟧ t v

⟦⌈⌉⟧∘norm t v = begin
  ⟦⌈_⌉⟧ (norm t) v
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (propagateIfCond (normConv t)) v
    ≡⟨ ⟦⌈⌉⟧∘propagateIfCond (normConv t) v ⟩
  ⟦⌈_⌉⟧ (normConv t) v
    ≡⟨ ⟦⌈⌉⟧∘normConv t v ⟩
  ⟦_⟧ t v
  ∎

--
