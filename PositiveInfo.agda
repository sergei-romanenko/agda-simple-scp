module PosInfoProp where

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
    (NCons (NSelCmp (sels ++ [ HD ])) (NSelCmp (sels ++ [ TL ])))


-- propagateIfCond

propagateIfCond : (nt : NTrm) → NTrm

propagateIfCond NNil = NNil
propagateIfCond (NCons nt1 nt2) =
  NCons (propagateIfCond nt1) (propagateIfCond nt2)
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
      ≡⟨ cong (flip NCons (NSelCmp (sels2 ++ [ TL ])))
              (cong (flip normNCmpSels sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ HD ])) ⟩
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
      ≡⟨ cong (NCons (NSelCmp (sels2 ++ [ HD ])))
              (cong (flip normNCmpSels sels2)
                    (sym $ setNilAtPreservesEval′ sels1 [ TL ])) ⟩
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
        ≡⟨ cong (flip normNCmpSels sels2)
                (sym $ setConsAtPreservesEval′ sels1 [ HD ]) ⟩
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
    ≡⟨ cong (flip evalNT v)
            (cong (flip normSelsNCmp sels1)
                  (replaceAt∘++ sels1 sels2 (NSelCmp []) NNil)) ⟩
  evalNT (normSelsNCmp (replaceAt sels1 (NSelCmp [])
                       (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil))
                       sels1) v
    ≡⟨ cong (flip evalNT v)
            (normSelsNCmp∘replaceAt sels1 (NSelCmp [])
              (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil)) ⟩
  evalNT (replaceAt sels2 (normSelsNCmp (NSelCmp []) sels1) NNil) v
    ≡⟨ cong (flip evalNT v)
            (cong (flip (replaceAt sels2) NNil)
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
    ≡⟨ cong (flip evalNT v)
            (cong (flip normSelsNCmp sels1)
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
    ≡⟨ cong (flip evalNT v)
            (cong (flip (replaceAt sels2)
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

-- evalNT∘setNilAt

VBottom≢VNil : VBottom ≢ VNil
VBottom≢VNil = λ ()

VCons≢VNil : ∀ {v1 v2} → VCons v1 v2 ≢ VNil
VCons≢VNil = λ ()

VCons≢VBottom : ∀ {v1 v2} → VCons v1 v2 ≢ VBottom
VCons≢VBottom = λ ()

evalNT∘setNilAt : (sels : List Selector) (v : Val) →
  evalSels v sels ≡ VNil → evalNT (setNilAt sels) v ≡ v

evalNT∘setNilAt [] VNil h = refl

evalNT∘setNilAt (sel ∷ sels) VNil h
  rewrite evalSels-VBottom sels
  = ⊥-elim (VBottom≢VNil h)

evalNT∘setNilAt [] (VCons v1 v2) h =
  ⊥-elim (VCons≢VNil h)

evalNT∘setNilAt (HD ∷ sels) (VCons v1 v2) h =
  cong (flip VCons v2) helper
  where
  helper = begin
    evalNT (replaceAt sels (NSelCmp [ HD ]) NNil) (VCons v1 v2)
      ≡⟨ cong (flip evalNT (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ HD ] NNil) ⟩
    evalNT (normSelsNCmp (replaceAt ([ HD ] ++ sels) (NSelCmp []) NNil) [ HD ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (evalNT (replaceAt ([ HD ] ++ sels) (NSelCmp []) NNil)
                     (VCons v1 v2)) [ HD ]
      ≡⟨ refl ⟩
    evalSels (evalNT (setNilAt ([ HD ] ++ sels)) (VCons v1 v2)) [ HD ]
      ≡⟨ setNilAtPreservesEval′′ (VCons v1 v2) [ HD ] sels ⟩
    evalNT (setNilAt sels) (evalSels (VCons v1 v2) [ HD ])
      ≡⟨ refl ⟩
    evalNT (setNilAt sels) v1
      ≡⟨ evalNT∘setNilAt sels v1 h ⟩
    v1
    ∎

evalNT∘setNilAt (TL ∷ sels) (VCons v1 v2) h =
  cong (VCons v1) helper
  where
  helper = begin
    evalNT (replaceAt sels (NSelCmp [ TL ]) NNil) (VCons v1 v2)
      ≡⟨ cong (flip evalNT (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ TL ] NNil) ⟩
    evalNT (normSelsNCmp (replaceAt ([ TL ] ++ sels) (NSelCmp []) NNil) [ TL ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (evalNT (replaceAt ([ TL ] ++ sels) (NSelCmp []) NNil)
                     (VCons v1 v2)) [ TL ]
      ≡⟨ refl ⟩
    evalSels (evalNT (setNilAt ([ TL ] ++ sels)) (VCons v1 v2)) [ TL ]
      ≡⟨ setNilAtPreservesEval′′ (VCons v1 v2) [ TL ] sels ⟩
    evalNT (setNilAt sels) (evalSels (VCons v1 v2) [ TL ])
      ≡⟨ refl ⟩
    evalNT (setNilAt sels) v2
      ≡⟨ evalNT∘setNilAt sels v2 h ⟩
    v2
    ∎

evalNT∘setNilAt sels VBottom h
  rewrite evalSels-VBottom sels
  = ⊥-elim (VBottom≢VNil h)

-- evalNT∘setConsAt

evalNT∘setConsAt : (sels : List Selector) (v u1 u2 : Val) →
  evalSels v sels ≡ VCons u1 u2 → evalNT (setConsAt sels) v ≡ v

evalNT∘setConsAt [] VNil u1 u2 h = ⊥-elim (VCons≢VNil (sym h))

evalNT∘setConsAt (sel ∷ sels) VNil u1 u2 h
  rewrite evalSels-VBottom sels
  = ⊥-elim (VCons≢VBottom (sym h))

evalNT∘setConsAt [] (VCons v1 v2) u1 u2 h = refl

evalNT∘setConsAt (HD ∷ sels) (VCons v1 v2) u1 u2 h =
  cong (flip VCons v2) helper
  where
  helper = begin
    evalNT (replaceAt sels (NSelCmp [ HD ])
                      (NCons (NSelCmp ((HD ∷ sels) ++ [ HD ]))
                             (NSelCmp ((HD ∷ sels) ++ [ TL ]))))
      (VCons v1 v2)
      ≡⟨ cong (flip evalNT (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ HD ]
                                 (NCons (NSelCmp (HD ∷ sels ++ [ HD ]))
                                        (NSelCmp (HD ∷ sels ++ [ TL ])))) ⟩
    evalNT (normSelsNCmp (replaceAt ([ HD ] ++ sels) (NSelCmp [])
                                    (NCons (NSelCmp (HD ∷ sels ++ [ HD ]))
                                           (NSelCmp (HD ∷ sels ++ [ TL ]))))
                         [ HD ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (evalNT (replaceAt ([ HD ] ++ sels) (NSelCmp [])
                                (NCons (NSelCmp (HD ∷ sels ++ [ HD ]))
                                       (NSelCmp (HD ∷ sels ++ [ TL ]))))
                     (VCons v1 v2))
             [ HD ]
      ≡⟨ refl ⟩
    evalSels (evalNT (setConsAt ([ HD ] ++ sels)) (VCons v1 v2)) [ HD ]
      ≡⟨ setConsAtPreservesEval′′ (VCons v1 v2) (HD ∷ []) sels ⟩
    evalNT (setConsAt sels) (evalSels v1 [])
      ≡⟨ refl ⟩
    evalNT (setConsAt sels) v1
      ≡⟨ evalNT∘setConsAt sels v1 u1 u2 h ⟩
    v1
    ∎

evalNT∘setConsAt (TL ∷ sels) (VCons v1 v2) v3 v4 h =
  cong (VCons v1) helper
  where
  helper = begin
    evalNT ((replaceAt sels (NSelCmp (TL ∷ []))
                       (NCons (NSelCmp (TL ∷ sels ++ [ HD ]))
                              (NSelCmp (TL ∷ sels ++ [ TL ])))))
           (VCons v1 v2)
      ≡⟨ cong (flip evalNT (VCons v1 v2))
              (replaceAt∘NSelCmp sels [ TL ]
                                 (NCons (NSelCmp (TL ∷ sels ++ [ HD ]))
                                        (NSelCmp (TL ∷ sels ++ [ TL ])))) ⟩
    evalNT (normSelsNCmp (replaceAt ([ TL ] ++ sels) (NSelCmp [])
                                    (NCons (NSelCmp (TL ∷ sels ++ [ HD ]))
                                           (NSelCmp (TL ∷ sels ++ [ TL ]))))
                         [ TL ])
           (VCons v1 v2)
      ≡⟨ refl ⟩
    evalSels (evalNT (replaceAt ([ TL ] ++ sels) (NSelCmp [])
                                (NCons (NSelCmp (TL ∷ sels ++ [ HD ]))
                                       (NSelCmp (TL ∷ sels ++ [ TL ]))))
                     (VCons v1 v2))
             [ TL ]
      ≡⟨ refl ⟩
    evalSels (evalNT (setConsAt ([ TL ] ++ sels)) (VCons v1 v2)) [ TL ]
      ≡⟨ setConsAtPreservesEval′′ (VCons v1 v2) (TL ∷ []) sels ⟩
    evalNT (setConsAt sels) (evalSels v2 [])
      ≡⟨ refl ⟩
    evalNT (setConsAt sels) v2
      ≡⟨ evalNT∘setConsAt sels v2 v3 v4 h ⟩
    v2
    ∎

evalNT∘setConsAt sels VBottom v1 v2 h
  rewrite  evalSels-VBottom sels
  = ⊥-elim (VCons≢VBottom (sym h))

-- condPropagatorsPreserveEval

condPropagatorsPreserveEval :
  (sels : List Selector) (nt1 nt2 : NTrm) (v : Val) →
    evalNT (NIfNil sels (normNCmp nt1 (setNilAt sels))
                        (normNCmp nt2 (setConsAt sels))) v
  ≡
  evalNT (NIfNil sels nt1 nt2) v

condPropagatorsPreserveEval sels nt1 nt2 v
  rewrite evalT∘sels2trm sels v
  with evalSels v sels | inspect (evalSels v) sels 

... | VNil | [ ≡VNil ]ⁱ = begin
  evalNT (normNCmp nt1 (setNilAt sels)) v
    ≡⟨ evalNT∘normNCmp nt1 (setNilAt sels) v ⟩
  evalNT nt1 (evalNT (setNilAt sels) v)
    ≡⟨ cong (evalNT nt1) (evalNT∘setNilAt sels v ≡VNil) ⟩
  evalNT nt1 v
  ∎

... | VCons _ _ | [ ≡VCons ]ⁱ = begin
  evalNT (normNCmp nt2 (setConsAt sels)) v
    ≡⟨ evalNT∘normNCmp nt2 (setConsAt sels) v ⟩
  evalNT nt2 (evalNT (setConsAt sels) v)
    ≡⟨ cong (evalNT nt2) (evalNT∘setConsAt sels v _ _ ≡VCons) ⟩
  evalT (ntrm2trm nt2) v   
  ∎

... | VBottom | _ = refl

--
-- evalNT∘propagateIfCond
--

evalNT∘propagateIfCond : (nt : NTrm) (v : Val) →
  evalNT (propagateIfCond nt) v ≡ evalNT nt v

evalNT∘propagateIfCond NNil v = refl

evalNT∘propagateIfCond (NCons nt1 nt2) v
  rewrite evalNT∘propagateIfCond nt1 v
        | evalNT∘propagateIfCond nt2 v
 = refl

evalNT∘propagateIfCond (NSelCmp sels) v = refl

evalNT∘propagateIfCond (NIfNil sels nt1 nt2) v = begin
  evalNT (propagateIfCond (NIfNil sels nt1 nt2)) v
    ≡⟨ refl ⟩
  evalNT (NIfNil sels (normNCmp (propagateIfCond nt1) (setNilAt sels))
                      (normNCmp (propagateIfCond nt2) (setConsAt sels))) v
    ≡⟨ refl ⟩
  ifNil (evalT (sels2trm sels) v)
        (evalNT (normNCmp (propagateIfCond nt1) (setNilAt sels)) v)
        (evalNT (normNCmp (propagateIfCond nt2) (setConsAt sels)) v)
    ≡⟨ cong₂ (ifNil (evalT (sels2trm sels) v))
             (evalNT∘normNCmp (propagateIfCond nt1) (setNilAt sels) v)
             (evalNT∘normNCmp (propagateIfCond nt2) (setConsAt sels) v) ⟩
  ifNil (evalT (sels2trm sels) v)
        (evalNT (propagateIfCond nt1) (evalNT (setNilAt sels) v))
        (evalNT (propagateIfCond nt2) (evalNT (setConsAt sels) v))
    ≡⟨ cong₂ (ifNil (evalT (sels2trm sels) v))
             (evalNT∘propagateIfCond nt1 (evalNT (setNilAt sels) v))
             (evalNT∘propagateIfCond nt2 (evalNT (setConsAt sels) v)) ⟩
  ifNil (evalT (sels2trm sels) v)
        (evalNT nt1 (evalNT (setNilAt sels) v))
        (evalNT nt2 (evalNT (setConsAt sels) v))
    ≡⟨ cong₂ (ifNil (evalT (sels2trm sels) v))
             (sym $ evalNT∘normNCmp nt1 (setNilAt sels) v)
             (sym $ evalNT∘normNCmp nt2 (setConsAt sels) v) ⟩
  ifNil (evalT (sels2trm sels) v)
        (evalNT (normNCmp nt1 (setNilAt sels)) v)
        (evalNT (normNCmp nt2 (setConsAt sels)) v)
    ≡⟨ refl ⟩
  evalNT (NIfNil sels (normNCmp nt1 (setNilAt sels))
                      (normNCmp nt2 (setConsAt sels))) v
    ≡⟨ condPropagatorsPreserveEval sels nt1 nt2 v ⟩
  evalNT (NIfNil sels nt1 nt2) v
  ∎

evalNT∘propagateIfCond NBottom v = refl

--
-- norm
--

-- We can combine the first two stages - normalization and
-- positive information propagation - into a single function,
-- and trivially establish its correctness.

norm : (t : Trm) → NTrm
norm t = propagateIfCond (normConv t)

-- evalNT∘norm

evalNT∘norm : ∀ t v → evalNT (norm t) v ≡ evalT t v

evalNT∘norm t v = begin
  evalNT (norm t) v
    ≡⟨ refl ⟩
  evalNT (propagateIfCond (normConv t)) v
    ≡⟨ evalNT∘propagateIfCond (normConv t) v ⟩
  evalNT (normConv t) v
    ≡⟨ evalNT∘normConv t v ⟩
  evalT t v
  ∎

--