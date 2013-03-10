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

evalSels [] v = v
evalSels (x ∷ xs) v = evalSels xs (evalSel x v)

evalSelsIsFoldl : ∀ sels v →
  evalSels sels v ≡ foldl (flip evalSel) v sels
evalSelsIsFoldl [] v = refl
evalSelsIsFoldl (x ∷ xs) v = evalSelsIsFoldl xs (evalSel x v)

-- ifNil

ifNil : (v0 v1 v2 : Val) → Val

ifNil VNil v1 v2 = v1
ifNil (VCons _ _) v1 v2 = v2
ifNil VBottom v1 v2 = VBottom

ifNil-cong : ∀ {v0 v0′ v1 v1′ v2 v2′ : Val} → v0 ≡ v0′ → v1 ≡ v1′ → v2 ≡ v2′ →
  ifNil v0 v1 v2 ≡ ifNil v0′ v1′ v2′
ifNil-cong refl refl refl = refl

ifNil-comm : ∀ (f : Val → Val) → f VBottom ≡ VBottom → ∀ v0 {v1 v2} →
  f (ifNil v0 v1 v2) ≡ ifNil v0 (f v1) (f v2)
ifNil-comm f fb VNil = refl
ifNil-comm f fb (VCons v1 v2) = refl
ifNil-comm f fb VBottom = fb

-- evalT

evalT : (t : Trm) (v : Val) →  Val

evalT Nil v = VNil
evalT (Cons t1 t2) v = VCons (evalT t1 v) (evalT t2 v)
evalT (Sel sel) v = evalSel sel v
evalT Id v = v
evalT (Cmp t1 t2) v = evalT t1 (evalT t2 v)
evalT (IfNil t0 t1 t2) v =
  ifNil (evalT t0 v) (evalT t1 v) (evalT t2 v) 
evalT Bottom v = VBottom

-- NTrm

data NTrm : Set where
  NNil    : NTrm 
  NCons   : (nt1 : NTrm) → (nt2 : NTrm) → NTrm 
  NSelCmp : (sels : List Selector) → NTrm
  NIfNil  : (sels : List Selector) → (nt1 : NTrm) → (nt2 : NTrm) → NTrm
  NBottom : NTrm

-- sel2trm

sel2trm : (t : Trm) → (sel : Selector) → Trm
sel2trm Id sel = Sel sel
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
      ≡⟨ helper (foldr (flip sel2trm) Id rsels)  ⟩
{-
    evalT (Cmp (Sel sel) (foldr (flip sel2trm) Id rsels)) v
      ≡⟨ refl ⟩
-}
    evalSel sel (evalT (foldr (flip sel2trm) Id rsels) v)
      ≡⟨ cong (evalSel sel) (lem-evalT-sels2trm-r rsels v) ⟩

    evalSel sel (foldr evalSel v rsels)
      ≡⟨ refl ⟩
    foldr evalSel v (sel ∷ rsels)
  ∎
  where
    helper : ∀ t → evalT (sel2trm t sel) v ≡ evalSel sel (evalT t v)
    helper Id = refl
    helper Nil = refl
    helper (Cons t1 t2) = refl
    helper (Sel sel') = refl
    helper (Cmp t1 t2) = refl
    helper (IfNil t0 t1 t2) = refl
    helper Bottom = refl

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
      ≡⟨ sym $ evalSelsIsFoldl sels v ⟩
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
    ifNil (evalT (sels2trm sels) v)
          (evalNT (normSelNCmp sel nt1) v)
          (evalNT (normSelNCmp sel nt2) v)
      ≡⟨ ifNil-cong
           (begin evalT (sels2trm sels) v ∎)
           (lem-normSelNCmpPreservesEval sel nt1 v)
           (lem-normSelNCmpPreservesEval sel nt2 v) ⟩
    ifNil (evalT (sels2trm sels) v)
          (evalSel sel (evalNT nt1 v))
          (evalSel sel (evalNT nt2 v))
      ≡⟨ sym $ ifNil-comm (evalSel sel) refl (evalT (sels2trm sels) v) ⟩
    evalSel sel (ifNil (evalT (sels2trm sels) v) (evalNT nt1 v) (evalNT nt2 v))
      ≡⟨ refl ⟩
    evalSel sel (evalNT (NIfNil sels nt1 nt2) v)
  ∎

lem-normSelNCmpPreservesEval sel NBottom v = refl

-- normSelsNCmp

normSelsNCmp : (sels : List Selector) (nt : NTrm) → NTrm
normSelsNCmp sels nt =
  foldl (λ nt sel → normSelNCmp sel nt) nt sels

-- lem-normSelsNCmpPreservesEvalT

lem-normSelsNCmpPreservesEvalT :
  ∀ (sels : List Selector) (nt : NTrm) (v : Val) →
          evalNT (normSelsNCmp sels nt) v ≡
          evalSels sels (evalNT nt v)

lem-normSelsNCmpPreservesEvalT [] nt v = refl

lem-normSelsNCmpPreservesEvalT (sel ∷ sels) nt v =
  begin
    evalNT (normSelsNCmp (sel ∷ sels) nt) v
      ≡⟨ refl ⟩
    evalNT (normSelsNCmp sels (normSelNCmp sel nt)) v
      ≡⟨ refl ⟩
    evalNT (normSelsNCmp sels (normSelNCmp sel nt)) v
      ≡⟨ lem-normSelsNCmpPreservesEvalT sels (normSelNCmp sel nt) v ⟩
    evalSels sels (evalNT (normSelNCmp sel nt) v)
      ≡⟨ cong (evalSels sels)
              (lem-normSelNCmpPreservesEval sel nt v) ⟩
    evalSels sels (evalSel sel (evalNT nt v))
      ≡⟨ refl ⟩
    evalSels (sel ∷ sels) (evalNT nt v)
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
lem-normSelsNCmp-NSelCmp [] sels2
  rewrite ++-[] (sels2)
  = refl
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

-- normNCmpSels

normNCmpSels : (nt : NTrm) (sels : List Selector) → NTrm

normNCmpSels NNil sels = NNil
normNCmpSels (NCons nt1 nt2) sels =
  NCons (normNCmpSels nt1 sels) (normNCmpSels nt2 sels)
normNCmpSels (NSelCmp sels2) sels = NSelCmp (sels ++ sels2)
normNCmpSels (NIfNil sels2 nt1 nt2) sels =
  NIfNil (sels ++ sels2) (normNCmpSels nt1 sels) (normNCmpSels nt2 sels)
normNCmpSels NBottom sels = NBottom

-- lem-normNCmpSelsPreservesEval

lem-normNCmpSelsPreservesEval :
  ∀ (sels : List Selector) (nt : NTrm) (v : Val) →
    evalNT (normNCmpSels nt sels) v ≡ evalNT nt (evalSels sels v)

lem-normNCmpSelsPreservesEval sels NNil v = refl

lem-normNCmpSelsPreservesEval sels (NCons nt1 nt2) v
  rewrite lem-normNCmpSelsPreservesEval sels nt1 v
        | lem-normNCmpSelsPreservesEval sels nt2 v = refl

lem-normNCmpSelsPreservesEval sels (NSelCmp sels0) v
  rewrite lem-evalT-sels2trm (sels ++ sels0) v
        | lem-evalSelsAppend sels sels0 v
        | lem-evalT-sels2trm sels0 (evalSels sels v)
  = refl
{-
  =
  begin
    evalNT (normNCmpSels (NSelCmp sels0) sels) v
      ≡⟨ refl ⟩
    evalNT (sels ++ sels0) v
      ≡⟨ lem-evalT-sels2trm (sels ++ sels0) v ⟩
    evalSels (sels ++ sels0) v
      ≡⟨ lem-evalSelsAppend sels sels0 v ⟩
    evalSels sels0 (evalSels sels v)
      ≡⟨ sym (lem-evalT-sels2trm sels0 (evalSels sels v)) ⟩
    evalNT (NSelCmp sels0) (evalSels sels v)
  ∎
-}

lem-normNCmpSelsPreservesEval sels (NIfNil sels0 nt1 nt2) v
  rewrite lem-evalT-sels2trm (sels ++ sels0) v
        | lem-evalT-sels2trm sels0 (evalSels sels v)
        | lem-evalSelsAppend sels sels0 v
  --= {!!} -- helper (evalSels sels0 (evalSels sels v))
  = ifNil-cong (begin evalSels sels0 (evalSels sels v) ∎)
               (lem-normNCmpSelsPreservesEval sels nt1 v)
               (lem-normNCmpSelsPreservesEval sels nt2 v)

lem-normNCmpSelsPreservesEval sels NBottom v = refl

-- lem-normNCmpSels-app

lem-normNCmpSels-app : ∀ (sels1 sels2 : List Selector) (nt : NTrm) →
  normNCmpSels nt (sels1 ++ sels2) ≡
  normNCmpSels (normNCmpSels nt sels2) sels1

lem-normNCmpSels-app sels1 sels2 NNil = refl
lem-normNCmpSels-app sels1 sels2 (NCons nt1 nt2)
  rewrite lem-normNCmpSels-app sels1 sels2 nt2
        | lem-normNCmpSels-app sels1 sels2 nt1
  = refl
{-
  =
  begin
    NCons (normNCmpSels nt1 (sels1 ++ sels2))
          (normNCmpSels nt2 (sels1 ++ sels2))
    ≡⟨ cong (NCons (normNCmpSels nt1 (sels1 ++ sels2)))
            (lem-normNCmpSels-app sels1 sels2 nt2) ⟩
    NCons (normNCmpSels nt1 (sels1 ++ sels2))
          (normNCmpSels (normNCmpSels nt2 sels2) sels1)
    ≡⟨ cong (λ z → NCons z (normNCmpSels (normNCmpSels nt2 sels2) sels1))
            (lem-normNCmpSels-app sels1 sels2 nt1) ⟩
    NCons (normNCmpSels (normNCmpSels nt1 sels2) sels1)
           (normNCmpSels (normNCmpSels nt2 sels2) sels1)
  ∎
-}

lem-normNCmpSels-app sels1 sels2 (NSelCmp sels)
  rewrite ++-assoc sels1 sels2 sels
  =  refl

lem-normNCmpSels-app sels1 sels2 (NIfNil sels nt1 nt2)
  rewrite ++-assoc sels1 sels2 sels
        | lem-normNCmpSels-app sels1 sels2 nt1
        | lem-normNCmpSels-app sels1 sels2 nt2
  = refl

lem-normNCmpSels-app sels1 sels2 NBottom = refl

-- normNIf

normNIf : (nt0 nt1 nt2 : NTrm) → NTrm

normNIf NNil nt1 nt2 =
  nt1
normNIf (NCons nt' nt'') nt1 nt2 =
  nt2
normNIf (NSelCmp sels) nt1 nt2 =
  NIfNil sels nt1 nt2
normNIf (NIfNil sels nt' nt'') nt1 nt2 =
  NIfNil sels (normNIf nt' nt1 nt2) (normNIf nt'' nt1 nt2)
normNIf NBottom nt1 nt2 =
  NBottom

-- normNIfPreservesEvalT

lem-normNIfPreservesEvalT : ∀ (nt1 nt2 nt3 : NTrm) (v : Val) →
  evalNT (normNIf nt1 nt2 nt3) v ≡
    ifNil (evalNT nt1 v) (evalNT nt2 v) (evalNT nt3 v)

lem-normNIfPreservesEvalT NNil nt2 nt3 v = refl
lem-normNIfPreservesEvalT (NCons nt' nt'') nt2 nt3 v = refl
lem-normNIfPreservesEvalT (NSelCmp sels) nt2 nt3 v
  with evalT (sels2trm sels) v
... | VNil = refl
... | VCons v1 v2 = refl
... | VBottom = refl
lem-normNIfPreservesEvalT (NIfNil sels nt' nt'') nt2 nt3 v
  with evalT (sels2trm sels) v
... | VNil        rewrite lem-normNIfPreservesEvalT nt'  nt2 nt3 v = refl
... | VCons v1 v2 rewrite lem-normNIfPreservesEvalT nt'' nt2 nt3 v = refl
... | VBottom = refl
lem-normNIfPreservesEvalT NBottom nt2 nt3 v = refl

-- lem-normNIfPreservesEval

lem-normNIfPreservesEval : ∀ (nt1 nt2 nt3 : NTrm) (v : Val) →
  evalNT (normNIf nt1 nt2 nt3) v ≡
    ifNil (evalNT nt1 v) (evalNT nt2 v) (evalNT nt3 v)

lem-normNIfPreservesEval nt1 nt2 nt3 v =
  lem-normNIfPreservesEvalT nt1 nt2 nt3 v

-- normNCmp

normNCmp : NTrm → NTrm → NTrm

{-
normNCmp nt1 nt2 with nt1
... | NNil = NNil
... | NCons nt' nt'' =
  NCons (normNCmp nt' nt2) (normNCmp nt'' nt2)
... | NSelCmp sels =
  normSelsNCmp sels nt2
... | NBottom = NBottom
... | NIfNil sels nt' nt'' with nt2
... | NSelCmp sels2 =
        NIfNil (sels2 ++ sels)
               (normNCmpSels nt' sels2) (normNCmpSels nt'' sels2)
... | NIfNil sels2 nt2' nt2'' =
        NIfNil sels2 (normNCmp nt1 nt2') (normNCmp nt1 nt2'')
... | _ =
        normNIf (normSelsNCmp sels nt2) (normNCmp nt' nt2) (normNCmp nt'' nt2)
-}

normNCmp NNil nt2 =
  NNil
normNCmp (NCons nt' nt'') nt2 =
  NCons (normNCmp nt' nt2) (normNCmp nt'' nt2)
normNCmp (NSelCmp sels) nt2 =
  normSelsNCmp sels nt2
normNCmp (NIfNil sels nt' nt'') NNil =
  normNIf (normSelsNCmp sels NNil) (normNCmp nt' NNil) (normNCmp nt'' NNil)
normNCmp (NIfNil sels nt' nt'') (NCons nt2' nt2'') =
  normNIf (normSelsNCmp sels (NCons nt2' nt2''))
    (normNCmp nt' (NCons nt2' nt2''))
    (normNCmp nt'' (NCons nt2' nt2''))
normNCmp (NIfNil sels nt' nt'') (NSelCmp sels2) =
  NIfNil (sels2 ++ sels) (normNCmpSels nt' sels2) (normNCmpSels nt'' sels2)
normNCmp (NIfNil sels nt' nt'') (NIfNil sels2 nt2' nt2'') =
  NIfNil sels2 (normNCmp (NIfNil sels nt' nt'') nt2')
               (normNCmp (NIfNil sels nt' nt'') nt2'')
normNCmp (NIfNil sels nt' nt'') NBottom =
  normNIf (normSelsNCmp sels NNil) (normNCmp nt' NNil) (normNCmp nt'' NNil)
normNCmp NBottom nt2 =
  NBottom

-- lem-normNCmpIfIf

lem-normNCmpIfIf : (sels1 sels2 : List Selector) →
  (nt1-1 nt1-2 nt2-1 nt2-2 : NTrm) →
  let nt1 = NIfNil sels1 nt1-1 nt1-2 in 
  normNCmp nt1 (NIfNil sels2 nt2-1 nt2-2)
    ≡ NIfNil sels2 (normNCmp nt1 nt2-1) (normNCmp nt1 nt2-2)
lem-normNCmpIfIf sels1 sels2 nt1-1 nt1-2 nt2-1 nt2-2 = refl

-- lem-normNCmpPreservesEval

lem-normNCmpPreservesEval : (nt1 nt2 : NTrm) (v : Val) →
  evalNT (normNCmp nt1 nt2) v ≡ evalNT nt1 (evalNT nt2 v)

lem-normNCmpPreservesEval NNil nt2 v =
  refl

lem-normNCmpPreservesEval (NCons nt' nt'') nt2 v
  rewrite lem-normNCmpPreservesEval nt' nt2 v
        | lem-normNCmpPreservesEval nt'' nt2 v
  = refl

lem-normNCmpPreservesEval (NSelCmp sels) nt2 v
  rewrite lem-normSelsNCmpPreservesEvalT sels nt2 v
        | sym (lem-evalT-sels2trm sels (evalT (ntrm2trm nt2) v))
  = refl
{-
  =
  begin
    evalNT (normNCmp (NSelCmp sels) nt2) v
      ≡⟨ refl ⟩
    evalT (ntrm2trm (normSelsNCmp sels nt2)) v
      ≡⟨ lem-normSelsNCmpPreservesEvalT sels nt2 v ⟩
    evalSels sels (evalT (ntrm2trm nt2) v)
      ≡⟨ sym (lem-evalT-sels2trm sels (evalT (ntrm2trm nt2) v)) ⟩
    evalT (sels2trm sels) (evalT (ntrm2trm nt2) v)
      ≡⟨ refl ⟩
    evalNT (NSelCmp sels) (evalNT nt2 v)
  ∎
-}

lem-normNCmpPreservesEval (NIfNil sels nt' nt'') nt2 v =

  begin
    evalNT (normNCmp (NIfNil sels nt' nt'') nt2) v
      ≡⟨ helper nt2 ⟩
    ifNil (evalNT (normSelsNCmp sels nt2) v)
          (evalNT (normNCmp nt' nt2) v) (evalNT (normNCmp nt'' nt2) v)
      ≡⟨ ifNil-cong (lem-normSelsNCmpPreservesEvalT sels nt2 v) refl refl ⟩
    ifNil (evalSels sels (evalNT nt2 v))
          (evalNT (normNCmp nt' nt2) v) (evalNT (normNCmp nt'' nt2) v)
      ≡⟨ ifNil-cong (sym $
           lem-evalT-sels2trm sels (evalT (ntrm2trm nt2) v))
           (lem-normNCmpPreservesEval nt' nt2 v)
           (lem-normNCmpPreservesEval nt'' nt2 v) ⟩
    ifNil (evalT (sels2trm sels) (evalNT nt2 v))
          (evalNT nt' (evalNT nt2 v)) (evalNT nt''(evalNT nt2 v))
      ≡⟨ refl ⟩
    evalNT (NIfNil sels nt' nt'') (evalNT nt2 v)
  ∎
  where
    helper : (nt2 : NTrm) →
      evalNT (normNCmp (NIfNil sels nt' nt'') nt2) v
      ≡
      ifNil (evalNT (normSelsNCmp sels nt2) v)
            (evalNT (normNCmp nt' nt2) v) (evalNT (normNCmp nt'' nt2) v)

    helper NNil = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') NNil) v
        ≡⟨ refl ⟩
      evalNT (normNIf (normSelsNCmp sels NNil)
                      (normNCmp nt' NNil) (normNCmp nt'' NNil)) v
        ≡⟨ lem-normNIfPreservesEval
             (normSelsNCmp sels NNil)
             (normNCmp nt' NNil) (normNCmp nt'' NNil) v ⟩
      ifNil (evalNT (normSelsNCmp sels NNil) v)
            (evalNT (normNCmp nt' NNil) v) (evalNT (normNCmp nt'' NNil) v)
      ∎

    helper (NCons nt1 nt3) = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') (NCons nt1 nt3)) v
        ≡⟨ refl ⟩
      evalNT (normNIf (normSelsNCmp sels (NCons nt1 nt3))
                      (normNCmp nt' (NCons nt1 nt3))
                      (normNCmp nt'' (NCons nt1 nt3))) v
        ≡⟨ lem-normNIfPreservesEval
             (normSelsNCmp sels (NCons nt1 nt3))
             (normNCmp nt' (NCons nt1 nt3)) (normNCmp nt'' (NCons nt1 nt3)) v ⟩
      ifNil (evalNT (normSelsNCmp sels (NCons nt1 nt3)) v)
            (evalNT (normNCmp nt' (NCons nt1 nt3)) v)
            (evalNT (normNCmp nt'' (NCons nt1 nt3)) v)
      ∎
    helper (NSelCmp sels') = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') (NSelCmp sels')) v
        ≡⟨ refl ⟩
      ifNil (evalT (sels2trm (sels' ++ sels)) v)
            (evalNT (normNCmpSels nt' sels') v)
            (evalNT (normNCmpSels nt'' sels') v)
        ≡⟨ ifNil-cong
             (lem-evalT-sels2trm (sels' ++ sels) v)
             (lem-normNCmpSelsPreservesEval sels' nt' v)
             (lem-normNCmpSelsPreservesEval sels' nt'' v) ⟩
      ifNil (evalSels (sels' ++ sels) v)
            (evalNT nt' (evalSels sels' v))
            (evalNT nt''(evalSels sels' v))
        ≡⟨ ifNil-cong
            (lem-evalSelsAppend sels' sels v)
            (sym $ cong (evalT (ntrm2trm nt')) (lem-evalT-sels2trm sels' v))
            (sym $ cong (evalT (ntrm2trm nt'')) (lem-evalT-sels2trm sels' v)) ⟩
      ifNil (evalSels sels (evalSels sels' v))
            (evalNT nt' (evalNT (NSelCmp sels') v))
            (evalNT nt'' (evalNT (NSelCmp sels') v))
        ≡⟨ ifNil-cong
             (cong (evalSels sels) (sym (lem-evalT-sels2trm sels' v)))
             (sym $ lem-normNCmpPreservesEval nt' (NSelCmp sels') v)
             (sym $ lem-normNCmpPreservesEval nt'' (NSelCmp sels') v) ⟩
      ifNil (evalSels sels (evalT (sels2trm sels') v))
            (evalNT (normNCmp nt' (NSelCmp sels')) v)
            (evalNT (normNCmp nt'' (NSelCmp sels')) v)
        ≡⟨ refl ⟩
      ifNil (evalSels sels (evalNT (NSelCmp sels') v))
            (evalNT (normNCmp nt' (NSelCmp sels')) v)
            (evalNT (normNCmp nt'' (NSelCmp sels')) v)
        ≡⟨ ifNil-cong
             (sym (lem-normSelsNCmpPreservesEvalT sels (NSelCmp sels') v))
             refl refl ⟩
      ifNil (evalNT (normSelsNCmp sels (NSelCmp sels')) v)
            (evalNT (normNCmp nt' (NSelCmp sels')) v)
            (evalNT (normNCmp nt'' (NSelCmp sels')) v)
      ∎

--lem-normSelsNCmpPreservesEvalT :
--  ∀ (sels : List Selector) (nt : NTrm) (v : Val) →
--          evalNT (normSelsNCmp sels nt) v ≡
--          evalSels sels (evalNT nt v)
--lem-normNIfPreservesEval : ∀ (nt1 nt2 nt3 : NTrm) (v : Val) →
--  evalNT (normNIf nt1 nt2 nt3) v ≡
--    ifNil (evalNT nt1 v) (evalNT nt2 v) (evalNT nt3 v)
--lem-evalT-sels2trm : ∀ sels v →
--  evalT (sels2trm sels) v ≡ evalSels sels v
--lem-evalSelsAppend : ∀ (sels1 sels2 : List Selector) (v : Val) →
--  evalSels (sels1 ++ sels2) v ≡ evalSels sels2 (evalSels sels1 v)
--lem-normNCmpSelsPreservesEval :
--  ∀ (sels : List Selector) (nt : NTrm) (v : Val) →
--    evalNT (normNCmpSels nt sels) v ≡ evalNT nt (evalSels sels v)
--lem-evalSelsVBottom : ∀ (sels : List Selector) →
--  evalSels sels VBottom ≡ VBottom

    helper (NIfNil sels' nt1 nt3) = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') (NIfNil sels' nt1 nt3)) v
        ≡⟨ {!!} ⟩
      evalNT (normNIf (normSelsNCmp sels (NIfNil sels' nt1 nt3))
                      (normNCmp nt' (NIfNil sels' nt1 nt3))
                      (normNCmp nt'' (NIfNil sels' nt1 nt3))) v
        ≡⟨ lem-normNIfPreservesEval
             (normSelsNCmp sels (NIfNil sels' nt1 nt3))
                           (normNCmp nt' (NIfNil sels' nt1 nt3))
                           (normNCmp nt'' (NIfNil sels' nt1 nt3)) v ⟩
      ifNil (evalNT (normSelsNCmp sels (NIfNil sels' nt1 nt3)) v)
            (evalNT (normNCmp nt' (NIfNil sels' nt1 nt3)) v)
            (evalNT (normNCmp nt'' (NIfNil sels' nt1 nt3)) v)
      ∎
    helper NBottom = {!!}
{-
      begin
      evalNT (normNCmp (NIfNil sels nt' nt'') NBottom) v
        ≡⟨ {!!} ⟩
      evalNT (normNIf (normSelsNCmp sels NBottom)
             (normNCmp nt' NBottom) (normNCmp nt'' NBottom)) v
        ≡⟨ lem-normNIfPreservesEval
             (normSelsNCmp sels NBottom)
             (normNCmp nt' NBottom) (normNCmp nt'' NBottom) v ⟩
      ifNil (evalNT (normSelsNCmp sels NBottom) v)
            (evalNT (normNCmp nt' NBottom) v)
            (evalNT (normNCmp nt'' NBottom) v)
        ≡⟨ {!!} ⟩
      ifNil (evalNT (normSelsNCmp sels NBottom) v)
            (evalNT nt' (evalNT NBottom v))
            (evalNT nt'' (evalNT NBottom v))
        ≡⟨ ifNil-cong
             (begin (evalNT (normSelsNCmp sels NBottom) v) ∎)
             (sym $ lem-normNCmpPreservesEval nt' NBottom v)
             (sym $ lem-normNCmpPreservesEval nt'' NBottom v) ⟩
      ifNil (evalNT (normSelsNCmp sels NBottom) v)
            (evalNT (normNCmp nt' NBottom) v)
            (evalNT (normNCmp nt'' NBottom) v)
      ∎
-}

lem-normNCmpPreservesEval NBottom nt2 v =
  refl


--
