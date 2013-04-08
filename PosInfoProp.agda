module PosInfoProp where

open import Data.List

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
    (NCons (NSelCmp (sels ++ [ HD ])) (NSelCmp (sels ++ [ TL ])))


-- propagateIfCond

propagateIfCond : (nt : NTrm) → NTrm

propagateIfCond nt with nt
... | NCons nt1 nt2 =
  NCons (propagateIfCond nt1) (propagateIfCond nt2)
... | NIfNil sels nt1 nt2 =
  NIfNil sels
    (normNCmp (propagateIfCond nt1) (setNilAt sels))
    (normNCmp (propagateIfCond nt2) (setConsAt sels))
... | _ = nt

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
    NCons (replaceAt sels1 (NSelCmp (sels2 ++ [ HD ])) NNil)
          (NSelCmp (sels2 ++ [ TL ]))
      ≡⟨ cong (flip NCons (NSelCmp (sels2 ++ [ TL ])))
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ HD ])) ⟩
    NCons (normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) (sels2 ++ [ HD ]))
          (NSelCmp (sels2 ++ [ TL ]))
      ≡⟨ cong (flip NCons (NSelCmp (sels2 ++ [ TL ])))
              (normNCmpSels∘++ (replaceAt sels1 (NSelCmp []) NNil)
                               sels2 [ HD ]) ⟩
    NCons (normNCmpSels
            (normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) [ HD ]) sels2)
          (NSelCmp (sels2 ++ [ TL ]))
      ≡⟨ sym $ cong ((flip NCons (NSelCmp (sels2 ++ [ TL ]))) ∘
                           (flip normNCmpSels sels2))
                    (setNilAtPreservesEval′ sels1 [ HD ]) ⟩
    NCons (normNCmpSels (replaceAt sels1 (NSelCmp [ HD ]) NNil) sels2)
          (NSelCmp (sels2 ++ [ TL ]))
      ≡⟨ refl ⟩
    normNCmpSels (replaceAt (HD ∷ sels1) (NSelCmp []) NNil) sels2
  ∎

setNilAtPreservesEval′ (TL ∷ sels1) sels2 =
  begin
    replaceAt (TL ∷ sels1) (NSelCmp sels2) NNil
      ≡⟨ refl ⟩
    NCons (NSelCmp (sels2 ++ [ HD ]))
          (replaceAt sels1 (NSelCmp (sels2 ++ [ TL ])) NNil)
      ≡⟨ cong (NCons (NSelCmp (sels2 ++ [ HD ])))
              (setNilAtPreservesEval′ sels1 (sels2 ++ [ TL ])) ⟩
    NCons (NSelCmp (sels2 ++ [ HD ]))
          (normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) (sels2 ++ [ TL ]))
      ≡⟨ cong (NCons (NSelCmp (sels2 ++ [ HD ])))
              (normNCmpSels∘++ (replaceAt sels1 (NSelCmp []) NNil)
                               sels2 (TL ∷ [])) ⟩
    NCons (NSelCmp (sels2 ++ [ HD ]))
          (normNCmpSels
            (normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) [ TL ]) sels2)
      ≡⟨ sym $ cong (NCons (NSelCmp (sels2 ++ [ HD ])) ∘
                                    (flip normNCmpSels sels2))
                    (setNilAtPreservesEval′ sels1 (TL ∷ [])) ⟩
    NCons (NSelCmp (sels2 ++ [ HD ]))
          (normNCmpSels (replaceAt sels1 (NSelCmp [ TL ]) NNil) sels2)
      ≡⟨ refl ⟩
    normNCmpSels (replaceAt (TL ∷ sels1) (NSelCmp []) NNil) sels2
  ∎

-- setConsAtPreservesEval′

setConsAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 (NSelCmp sels2)
            (NCons (NSelCmp (sels2 ++ sels1 ++ [ HD ]))
                   (NSelCmp (sels2 ++ sels1 ++ [ TL ])))
  ≡
  normNCmpSels (replaceAt sels1 (NSelCmp [])
                          (NCons (NSelCmp (sels1 ++ [ HD ]))
                                 (NSelCmp (sels1 ++ [ TL ]))))
               sels2

setConsAtPreservesEval′ [] sels2 = refl

setConsAtPreservesEval′ (HD ∷ sels1) sels2
  rewrite sym $ ++-assoc sels2 [ HD ] (sels1 ++ [ HD ])
        | sym $ ++-assoc sels2 [ HD ] (sels1 ++ [ TL ])
  = cong (flip NCons (NSelCmp (sels2 ++ [ TL ])))
         helper
  where
    helper = begin
      replaceAt sels1 (NSelCmp (sels2 ++ [ HD ]))
          (NCons (NSelCmp ((sels2 ++ [ HD ]) ++ sels1 ++ [ HD ]))
                 (NSelCmp ((sels2 ++ [ HD ]) ++ sels1 ++ [ TL ])))
        ≡⟨ setConsAtPreservesEval′ sels1 (sels2 ++ [ HD ]) ⟩
      normNCmpSels
          (replaceAt sels1 (NSelCmp [])
              (NCons (NSelCmp (sels1 ++ [ HD ]))
                     (NSelCmp (sels1 ++ [ TL ]))))
          (sels2 ++ [ HD ])
        ≡⟨ normNCmpSels∘++
             (replaceAt sels1 (NSelCmp [])
               (NCons (NSelCmp (sels1 ++ [ HD ]))
                      (NSelCmp (sels1 ++ [ TL ]))))
             sels2 (HD ∷ []) ⟩
      normNCmpSels
        (normNCmpSels
          (replaceAt sels1 (NSelCmp [])
                     (NCons (NSelCmp (sels1 ++ [ HD ]))
                            (NSelCmp (sels1 ++ [ TL ]))))
          (HD ∷ []))
        sels2
        ≡⟨ sym $ cong (flip normNCmpSels sels2)
                      (setConsAtPreservesEval′ sels1 [ HD ]) ⟩
      normNCmpSels
          (replaceAt sels1 (NSelCmp [ HD ])
            (NCons (NSelCmp ([ HD ] ++ sels1 ++ [ HD ]))
                   (NSelCmp ([ HD ] ++ sels1 ++ [ TL ]))))
          sels2
      ∎

setConsAtPreservesEval′ (TL ∷ sels1) sels2
  rewrite sym $ ++-assoc sels2 [ TL ] (sels1 ++ [ TL ])
        | sym $ ++-assoc sels2 [ TL ] (sels1 ++ [ HD ])
        | setConsAtPreservesEval′ sels1 (sels2 ++ [ TL ])
        | setConsAtPreservesEval′ sels1 [ TL ]
        | normNCmpSels∘++
             (replaceAt sels1 (NSelCmp [])
               (NCons (NSelCmp (sels1 ++ [ HD ]))
                      (NSelCmp (sels1 ++ [ TL ]))))
             sels2 (TL ∷ [])

  = refl

-- setNilAtPreservesEval′′

setNilAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  evalSels (evalNT (setNilAt (sels1 ++ sels2)) v) sels1
    ≡ evalNT (setNilAt sels2) (evalSels v sels1)

setNilAtPreservesEval′′ v sels1 sels2 = begin
  evalSels (evalNT (setNilAt (sels1 ++ sels2)) v) sels1
    ≡⟨ refl ⟩
  evalSels (evalNT (replaceAt (sels1 ++ sels2) (NSelCmp []) NNil) v) sels1
    ≡⟨ sym $ evalNT∘normSelsNCmp
               (replaceAt (sels1 ++ sels2) (NSelCmp []) NNil) sels1 v ⟩
  evalNT (normSelsNCmp (replaceAt (sels1 ++ sels2) (NSelCmp []) NNil) sels1) v
    ≡⟨ cong (flip evalNT v) (cong (flip normSelsNCmp sels1)
                  (replaceAt∘++ sels1 sels2 (NSelCmp []) NNil)) ⟩
  evalNT (normSelsNCmp (replaceAt sels1 (NSelCmp [])
                       (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil))
                       sels1) v
    ≡⟨ cong (flip evalNT v)
            (normSelsNCmp∘replaceAt sels1 (NSelCmp [])
              (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil)) ⟩
  evalNT (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil) v
    ≡⟨ cong (flip evalNT v) (cong (flip (replaceAt sels2) NNil)
                  (normSelsNCmp∘NSelCmp [] sels1)) ⟩
  evalNT (replaceAt sels2 (NSelCmp sels1) NNil) v
    ≡⟨ cong (flip evalNT v) (setNilAtPreservesEval′ sels2 sels1) ⟩
  evalNT (normNCmpSels (replaceAt sels2 (NSelCmp []) NNil) sels1) v
    ≡⟨ evalNT∘normNCmpSels (replaceAt sels2 (NSelCmp []) NNil) sels1 v ⟩
  evalNT (replaceAt sels2 (NSelCmp []) NNil) (evalSels v sels1)
    ≡⟨ refl ⟩
  evalNT (setNilAt sels2) (evalSels v sels1)
  ∎

-- setConsAtPreservesEval′′

setConsAtPreservesEval′′ : (v : Val) (sels1 sels2 : List Selector) →
  evalSels (evalNT (setConsAt (sels1 ++ sels2)) v) sels1
    ≡ evalNT (setConsAt sels2) (evalSels v sels1)

setConsAtPreservesEval′′ v sels1 sels2 = begin
  evalSels (evalNT (setConsAt (sels1 ++ sels2)) v) sels1
    ≡⟨ sym $ evalNT∘normSelsNCmp (setConsAt (sels1 ++ sels2)) sels1 v ⟩
  evalNT (normSelsNCmp (setConsAt (sels1 ++ sels2)) sels1) v
    ≡⟨ refl ⟩
  evalNT (normSelsNCmp (replaceAt (sels1 ++ sels2) (NSelCmp [])
                          (NCons (NSelCmp ((sels1 ++ sels2) ++ [ HD ]))
                           (NSelCmp ((sels1 ++ sels2) ++ [ TL ]))))
                       sels1) v
    ≡⟨ cong (flip evalNT v) (cong (flip normSelsNCmp sels1)
                  (replaceAt∘++ sels1 sels2 (NSelCmp [])
                    (NCons (NSelCmp ((sels1 ++ sels2) ++ [ HD ]))
                           (NSelCmp ((sels1 ++ sels2) ++ [ TL ]))))) ⟩
  evalNT (normSelsNCmp
           (replaceAt sels1 (NSelCmp [])
             (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1)
                        (NCons (NSelCmp ((sels1 ++ sels2) ++ [ HD ]))
                               (NSelCmp ((sels1 ++ sels2) ++ [ TL ])))))
           sels1) v
    ≡⟨ cong (flip evalNT v)
            (normSelsNCmp∘replaceAt sels1 (NSelCmp [])
              (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1)
                         (NCons (NSelCmp ((sels1 ++ sels2) ++ [ HD ]))
                                (NSelCmp ((sels1 ++ sels2) ++ [ TL ]))))) ⟩
  evalNT (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1)
            (NCons (NSelCmp ((sels1 ++ sels2) ++ [ HD ]))
                   (NSelCmp ((sels1 ++ sels2) ++ [ TL ])))) v
    ≡⟨ cong (flip evalNT v) (cong (flip (replaceAt sels2)
                         (NCons (NSelCmp ((sels1 ++ sels2) ++ [ HD ]))
                                (NSelCmp ((sels1 ++ sels2) ++ [ TL ]))))
            (normSelsNCmp∘NSelCmp [] sels1)) ⟩
  evalNT (replaceAt sels2
                    (NSelCmp sels1)
                    (NCons (NSelCmp ((sels1 ++ sels2) ++ [ HD ]))
                           (NSelCmp ((sels1 ++ sels2) ++ [ TL ])))) v
    ≡⟨ cong (flip evalNT v)
            (cong (replaceAt sels2 (NSelCmp sels1))
                  (cong (flip NCons (NSelCmp ((sels1 ++ sels2) ++ [ TL ])))
                        (cong NSelCmp (++-assoc sels1 sels2 [ HD ])))) ⟩
  evalNT (replaceAt sels2
                    (NSelCmp sels1)
                    (NCons (NSelCmp (sels1 ++ sels2 ++ [ HD ]))
                           (NSelCmp ((sels1 ++ sels2) ++ [ TL ])))) v
    ≡⟨ cong (flip evalNT v)
            (cong (replaceAt sels2 (NSelCmp sels1))
                  (cong (NCons (NSelCmp (sels1 ++ sels2 ++ [ HD ])))
                        (cong NSelCmp (++-assoc sels1 sels2 [ TL ])))) ⟩
  evalNT (replaceAt sels2
                    (NSelCmp sels1)
                    (NCons (NSelCmp (sels1 ++ sels2 ++ [ HD ]))
                           (NSelCmp (sels1 ++ sels2 ++ [ TL ])))) v
    ≡⟨ cong (flip evalNT v)
            (setConsAtPreservesEval′ sels2 sels1) ⟩
  evalNT (normNCmpSels
            (replaceAt sels2 (NSelCmp [])
                       (NCons (NSelCmp (sels2 ++ [ HD ]))
                              (NSelCmp (sels2 ++ [ TL ]))))
            sels1) v
    ≡⟨ refl ⟩
  evalNT (normNCmpSels (setConsAt sels2) sels1) v
    ≡⟨ evalNT∘normNCmpSels (setConsAt sels2) sels1 v ⟩
  evalNT (setConsAt sels2) (evalSels v sels1)
  ∎

{-
evalNT∘normNCmpSels :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    evalNT (normNCmpSels nt sels) v ≡ evalNT nt (evalSels v sels)

evalNT∘normSelsNCmp :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    evalNT (normSelsNCmp nt sels) v ≡
    evalSels (evalNT nt v) sels

normNCmpSels∘++ : (nt : NTrm) (sels1 sels2 : List Selector) →
  normNCmpSels nt (sels1 ++ sels2) ≡
  normNCmpSels (normNCmpSels nt sels2) sels1

normSelsNCmp∘NSelCmp : ∀ (sels1 sels2 : List Selector) →
  normSelsNCmp (NSelCmp sels1) sels2 ≡ NSelCmp (sels1 ++ sels2)

normSelsNCmp∘replaceAt : (sels : List Selector) (t t′ : NTrm) →
  normSelsNCmp (replaceAt sels t t′) sels ≡ t′

replaceAt∘++ : ∀ (sels1 sels2 : List Selector) (nt nt′ : NTrm) →
  replaceAt (sels1 ++ sels2) nt nt′
  ≡
  replaceAt sels1 nt (replaceAt sels2 (normSelsNCmp nt sels1) nt′)

setNilAtPreservesEval′ : (sels1 sels2 : List Selector) →
  replaceAt sels1 (NSelCmp sels2) NNil
    ≡ normNCmpSels (replaceAt sels1 (NSelCmp []) NNil) sels2

-}

--
