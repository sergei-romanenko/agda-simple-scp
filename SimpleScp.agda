module SimpleScp where

open import Data.List
open import Data.List.Reverse
open import Data.List.Properties
--open import Data.Nat hiding (compare)
open import Function
open import Relation.Binary.PropositionalEquality
  renaming([_] to [_]ⁱ)
open import Relation.Nullary
open import Relation.Binary
open ≡-Reasoning

open import Util

data Val : Set where
  VNil : Val
  VCons : (v1 : Val) → (v2 : Val) → Val
  VBottom : Val 

data Selector : Set where
  HD : Selector
  TL : Selector

data Trm : Set where
  Nil    : Trm
  Cons   : (t1 : Trm) → (t2 : Trm) → Trm 
  Sel    : (sel : Selector) → Trm
  Id     : Trm
  Cmp    : (t1 : Trm) → (t2 : Trm) → Trm
  IfNil  : (t0 : Trm) → (t1 : Trm) → (t2 : Trm) → Trm
  Bottom : Trm

-- evalSel

evalSel : (sel : Selector) → (v : Val) → Val
evalSel sel VNil = VBottom
evalSel sel VBottom = VBottom
evalSel HD (VCons v1 v2) = v1
evalSel TL (VCons v1 v2) = v2

--evalSels

evalSels : (sels : List Selector) (v : Val) → Val
evalSels sels v =
  foldl (flip evalSel) v sels

-- evalT

evalT : (t : Trm) (v : Val) →  Val
evalT-IfNil : (v0 : Val) (t1 t2 : Trm) (v : Val) →  Val

evalT Nil v = VNil
evalT (Cons t1 t2) v = VCons (evalT t1 v) (evalT t2 v)
evalT (Sel sel) v = evalSel sel v
evalT Id v = v
evalT (Cmp t1 t2) v = evalT t1 (evalT t2 v)
evalT (IfNil t0 t1 t2) v = evalT-IfNil (evalT t0 v) t1 t2 v
evalT Bottom v = VBottom

evalT-IfNil VNil t1 t2 v = evalT t1 v
evalT-IfNil (VCons v1 v2) t1 t2 v = evalT t2 v
evalT-IfNil VBottom t1 t2 v = VBottom

-- NTrm

data NTrm : Set where
  NNil    : NTrm 
  NCons   : (nt1 : NTrm) → (nt2 : NTrm) → NTrm 
  NSelCmp : (sels : List Selector) → NTrm
  NIfNil  : (sels : List Selector) → (nt1 : NTrm) → (nt2 : NTrm) → NTrm
  NBottom : NTrm

-- sel2trm

sel2trm : (t : Trm) → (sel : Selector) → Trm
--sel2trm Id sel = Sel sel
sel2trm t sel = Cmp (Sel sel) t

-- sels2trm

sels2trm : (sels : List Selector) → Trm
sels2trm sels = foldl sel2trm Id sels

-- ntrm2trm

ntrm2trm : (nt : NTrm) → Trm

ntrm2trm NNil = Nil
ntrm2trm (NCons nt1 nt2) = Cons (ntrm2trm nt1) (ntrm2trm nt2)
ntrm2trm (NSelCmp sels) = sels2trm sels
ntrm2trm (NIfNil sels nt1 nt2) =
  IfNil (sels2trm sels) (ntrm2trm nt1) (ntrm2trm nt2)
ntrm2trm NBottom = Bottom

-- evalNT

evalNT : (nt : NTrm) (v : Val) → Val
evalNT nt v = evalT (ntrm2trm nt) v

-- lem-evalT-sels2trm-r

lem-evalT-sels2trm-r : ∀ rsels v →
  evalT (foldr (flip sel2trm) Id rsels) v ≡
  foldr evalSel v rsels

lem-evalT-sels2trm-r [] v = refl

lem-evalT-sels2trm-r (sel ∷ rsels) v =
  begin
    evalT (foldr (flip sel2trm) Id (sel ∷ rsels)) v
      ≡⟨ refl ⟩
    evalT (sel2trm (foldr (flip sel2trm) Id rsels) sel) v
      ≡⟨ refl ⟩
    evalT (Cmp (Sel sel) (foldr (flip sel2trm) Id rsels)) v
      ≡⟨ refl ⟩
    evalSel sel (evalT (foldr (flip sel2trm) Id rsels) v)
      ≡⟨ cong (evalSel sel) (lem-evalT-sels2trm-r rsels v) ⟩
    evalSel sel (foldr evalSel v rsels)
      ≡⟨ refl ⟩
    foldr evalSel v (sel ∷ rsels)
  ∎

-- lem-evalT-sels2trm

lem-evalT-sels2trm : ∀ sels v →
  evalT (sels2trm sels) v ≡ evalSels sels v

lem-evalT-sels2trm sels v =
  begin
    evalT (sels2trm sels) v
      ≡⟨ refl ⟩
    evalT (foldl sel2trm Id sels) v
      ≡⟨ cong (λ e → evalT e v) (foldl⇒foldr-reverse sel2trm Id sels) ⟩
    evalT (foldr (flip sel2trm) Id (reverse sels)) v
      ≡⟨ lem-evalT-sels2trm-r (foldl (λ sels' sel → sel ∷ sels') [] sels) v ⟩
    foldr evalSel v (reverse sels)
      ≡⟨ sym (foldl⇒foldr-reverse (flip evalSel) v sels) ⟩
    foldl (flip evalSel) v sels
      ≡⟨ refl ⟩
    evalSels sels v
  ∎

-- lem-evalSelsVBottom

lem-evalSelsVBottom : ∀ (sels : List Selector) →
  evalSels sels VBottom ≡ VBottom

lem-evalSelsVBottom [] = refl
lem-evalSelsVBottom (sel ∷ sels) = lem-evalSelsVBottom sels

-- lem-evalSelsAppend

lem-evalSelsAppend : ∀ (sels1 sels2 : List Selector) (v : Val) →
  evalSels (sels1 ++ sels2) v ≡ evalSels sels2 (evalSels sels1 v)

lem-evalSelsAppend [] sels2 v = refl
lem-evalSelsAppend (sel ∷ xs) sels2 v =
  lem-evalSelsAppend xs sels2 (evalSel sel v)

-- normSelNCmp

normSelNCmp : (sel : Selector) (nt : NTrm) → NTrm

normSelNCmp sel NNil = NBottom
normSelNCmp HD (NCons nt1 nt2) = nt1
normSelNCmp TL (NCons nt1 nt2) = nt2
normSelNCmp sel (NSelCmp sels) = NSelCmp (sels ++ [ sel ])
normSelNCmp sel (NIfNil sels nt1 nt2) =
  NIfNil sels (normSelNCmp sel nt1) (normSelNCmp sel nt2)
normSelNCmp sel NBottom = NBottom

-- lem-normSelNCmpPreservesEval

lem-normSelNCmpPreservesEval : ∀ (sel : Selector) (nt : NTrm) (v : Val) →
  evalNT (normSelNCmp sel nt) v ≡ evalSel sel (evalNT nt v)

lem-normSelNCmpPreservesEval sel NNil v = refl
lem-normSelNCmpPreservesEval HD (NCons nt1 nt2) v = refl
lem-normSelNCmpPreservesEval TL (NCons nt1 nt2) v = refl

lem-normSelNCmpPreservesEval sel (NSelCmp sels) v =
  begin
    evalNT (normSelNCmp sel (NSelCmp sels)) v
      ≡⟨ refl ⟩
    evalNT (NSelCmp (sels ++ [ sel ])) v
      ≡⟨ refl ⟩
    evalT (ntrm2trm (NSelCmp (sels ++ [ sel ]))) v
      ≡⟨ refl ⟩
    evalT (sels2trm (sels ++ [ sel ])) v
      ≡⟨ lem-evalT-sels2trm (sels ++ [ sel ]) v ⟩
    evalSels (sels ++ [ sel ]) v
      ≡⟨ lem-evalSelsAppend sels [ sel ] v ⟩
    evalSels [ sel ] (evalSels sels v)
      ≡⟨ refl ⟩
    evalSel sel (evalSels sels v)
      ≡⟨ sym (cong (evalSel sel) (lem-evalT-sels2trm sels v)) ⟩
    evalSel sel (evalT (sels2trm sels) v)
      ≡⟨ refl ⟩
    evalSel sel (evalT (ntrm2trm (NSelCmp sels)) v)
      ≡⟨ refl ⟩
    evalSel sel (evalNT (NSelCmp sels) v)
  ∎

lem-normSelNCmpPreservesEval sel (NIfNil sels nt1 nt2) v =
  begin
    evalNT (normSelNCmp sel (NIfNil sels nt1 nt2)) v
      ≡⟨ refl ⟩
    evalNT (NIfNil sels (normSelNCmp sel nt1) (normSelNCmp sel nt2)) v
      ≡⟨ refl ⟩
    evalT (ntrm2trm (NIfNil sels (normSelNCmp sel nt1) (normSelNCmp sel nt2))) v
      ≡⟨ refl ⟩
    evalT (IfNil (sels2trm sels) (ntrm2trm (normSelNCmp sel nt1))
                                 (ntrm2trm (normSelNCmp sel nt2))) v
      ≡⟨ refl ⟩
    evalT-IfNil (evalT (sels2trm sels) v) (ntrm2trm (normSelNCmp sel nt1))
                                          (ntrm2trm (normSelNCmp sel nt2)) v
      ≡⟨ cong (λ t → evalT-IfNil t (ntrm2trm (normSelNCmp sel nt1))
                                    (ntrm2trm (normSelNCmp sel nt2)) v)
              (lem-evalT-sels2trm sels v) ⟩
    evalT-IfNil (evalSels sels v) (ntrm2trm (normSelNCmp sel nt1))
                                  (ntrm2trm (normSelNCmp sel nt2)) v
      ≡⟨ helper (evalSels sels v) ⟩

    evalSel sel (evalT-IfNil (evalSels sels v) (ntrm2trm nt1)
                                               (ntrm2trm nt2) v)
      ≡⟨ cong (λ t → evalSel sel (evalT-IfNil t (ntrm2trm nt1)
                                                 (ntrm2trm nt2) v))
              (sym (lem-evalT-sels2trm sels v)) ⟩
    evalSel sel (evalT-IfNil (evalT (sels2trm sels) v) (ntrm2trm nt1)
                                                       (ntrm2trm nt2) v)
      ≡⟨ refl ⟩
    evalSel sel (evalT (IfNil (sels2trm sels) (ntrm2trm nt1) (ntrm2trm nt2)) v)
      ≡⟨ refl ⟩
    evalSel sel (evalT (ntrm2trm (NIfNil sels nt1 nt2)) v)
      ≡⟨ refl ⟩
    evalSel sel (evalNT (NIfNil sels nt1 nt2) v)
  ∎
  where
    helper : ∀ (v0 : Val) →
      evalT-IfNil v0 (ntrm2trm (normSelNCmp sel nt1))
                     (ntrm2trm (normSelNCmp sel nt2)) v
      ≡
      evalSel sel (evalT-IfNil v0 (ntrm2trm nt1) (ntrm2trm nt2) v)
    helper VNil = lem-normSelNCmpPreservesEval sel nt1 v
    helper (VCons v1 v2) = lem-normSelNCmpPreservesEval sel nt2 v
    helper VBottom = refl

lem-normSelNCmpPreservesEval sel NBottom v = refl

-- normSelsNCmp

normSelsNCmp : (sels : List Selector) (nt : NTrm) → NTrm
normSelsNCmp sels nt =
  foldl (λ nt sel → normSelNCmp sel nt) nt sels

-- lem-normSelsNCmpPreservesEvalT

lem-normSelsNCmpPreservesEvalT :
  ∀ (sels : List Selector) (nt : NTrm) (v : Val) →
          evalT (ntrm2trm (normSelsNCmp sels nt)) v ≡
          evalSels sels (evalT (ntrm2trm nt) v)

lem-normSelsNCmpPreservesEvalT [] nt v = refl

lem-normSelsNCmpPreservesEvalT (sel ∷ sels) nt v =
  begin
    evalT (ntrm2trm (normSelsNCmp (sel ∷ sels) nt)) v
      ≡⟨ refl ⟩
    evalT (ntrm2trm (normSelsNCmp sels (normSelNCmp sel nt))) v
      ≡⟨ refl ⟩
    evalNT (normSelsNCmp sels (normSelNCmp sel nt)) v
      ≡⟨ lem-normSelsNCmpPreservesEvalT sels (normSelNCmp sel nt) v ⟩
    evalSels sels (evalNT (normSelNCmp sel nt) v)
      ≡⟨ cong (λ t → evalSels sels t)
              (lem-normSelNCmpPreservesEval sel nt v) ⟩
    evalSels sels (evalSel sel (evalNT nt v))
      ≡⟨ refl ⟩
    evalSels sels (evalSel sel (evalT (ntrm2trm nt) v))
      ≡⟨ refl ⟩
    evalSels (sel ∷ sels) (evalT (ntrm2trm nt) v)
  ∎

-- normSelsNCmpPreservesEval

normSelsNCmpPreservesEval :
  ∀ (sels : List Selector) (nt : NTrm) (v : Val) →
    evalNT (normSelsNCmp sels nt) v ≡ evalSels sels (evalNT nt v)

normSelsNCmpPreservesEval sels nt v =
  lem-normSelsNCmpPreservesEvalT sels nt v

-- lem-normSelsNCmp-NSelCmp

lem-normSelsNCmp-NSelCmp : ∀ (sels1 sels2 : List Selector) →
  normSelsNCmp sels1 (NSelCmp sels2) ≡ NSelCmp (sels2 ++ sels1)
lem-normSelsNCmp-NSelCmp [] sels2 rewrite ++-[] (sels2)  = refl
lem-normSelsNCmp-NSelCmp (sel ∷ sels1) sels2 =
  begin
    normSelsNCmp (sel ∷ sels1) (NSelCmp sels2)
      ≡⟨ refl ⟩
    normSelsNCmp sels1 (NSelCmp (sels2 ++ sel ∷ []))
      ≡⟨ lem-normSelsNCmp-NSelCmp sels1 (sels2 ++ sel ∷ []) ⟩
    NSelCmp ((sels2 ++ sel ∷ []) ++ sels1)
      ≡⟨ cong NSelCmp (++-assoc sels2 (sel ∷ []) sels1) ⟩
    NSelCmp (sels2 ++ (sel ∷ [] ++ sels1))
      ≡⟨ refl ⟩
    NSelCmp (sels2 ++ sel ∷ sels1)
  ∎

-- lem-normNCmpSels-app
{-
lem-normNCmpSels-app : ∀ (sels1 sels2 : List Selector) (nt : NTrm) →
  normNCmpSels nt (sels1 ++ sels2) ≡
  normNCmpSels (normNCmpSels nt sels2) sels1
lem-normNCmpSels-app sels1 sels2 nt = ?
-}