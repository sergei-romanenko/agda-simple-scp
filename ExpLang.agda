module ExpLang where

open import Data.List
open import Data.List.Reverse
open import Data.List.Properties
--open import Data.Nat hiding (compare)
open import Data.Unit
open import Data.Empty

open import Data.Product

open import Function
open import Relation.Binary.PropositionalEquality
  renaming([_] to [_]ⁱ)
open import Relation.Nullary
open import Relation.Binary
open ≡-Reasoning

open import Util

--
-- Simple expression language
--

infixr 5 _∷_
infixr 6 _$$_

data Val : Set where
  VNil : Val
  VCons : (v1 : Val) → (v2 : Val) → Val
  VBottom : Val 

data Selector : Set where
  HD : Selector
  TL : Selector

data Trm : Set where
  []     : Trm
  _∷_    : (t1 : Trm) → (t2 : Trm) → Trm 
  Sel    : (sel : Selector) → Trm
  Id     : Trm
  _$$_   : (t1 : Trm) → (t2 : Trm) → Trm
  IfNil  : (t0 : Trm) → (t1 : Trm) → (t2 : Trm) → Trm
  Bottom : Trm

-- Hd Tl

Hd = Sel HD
Tl = Sel TL

-- evalSel

evalSel : (v : Val) → (sel : Selector) → Val
evalSel VNil sel = VBottom
evalSel VBottom sel = VBottom
evalSel (VCons v1 v2) HD = v1
evalSel (VCons v1 v2) TL = v2

--evalSels

evalSels : (v : Val) (sels : List Selector) → Val

evalSels v [] = v
evalSels v (x ∷ xs) = evalSels (evalSel v x) xs

evalSelsIsFoldl : ∀ v sels →
  evalSels v sels ≡ foldl evalSel v sels
evalSelsIsFoldl v [] = refl
evalSelsIsFoldl v (x ∷ xs) = evalSelsIsFoldl (evalSel v x) xs

-- ifNil

ifNil : (v0 v1 v2 : Val) → Val

ifNil VNil v1 v2 = v1
ifNil (VCons _ _) v1 v2 = v2
ifNil VBottom v1 v2 = VBottom

ifNil-cong : ∀ {v0 v0′ v1 v1′ v2 v2′ : Val} → v0 ≡ v0′ → v1 ≡ v1′ → v2 ≡ v2′ →
  ifNil v0 v1 v2 ≡ ifNil v0′ v1′ v2′
ifNil-cong refl refl refl = refl

ifNil-distr : ∀ (f : Val → Val) → f VBottom ≡ VBottom → ∀ v0 {v1 v2} →
  f (ifNil v0 v1 v2) ≡ ifNil v0 (f v1) (f v2)
ifNil-distr f fb VNil = refl
ifNil-distr f fb (VCons v1 v2) = refl
ifNil-distr f fb VBottom = fb

ifNil∘ifNil : ∀ u0 {u1 u2 v1 v2} →
  ifNil (ifNil u0 u1 u2) v1 v2 ≡ ifNil u0 (ifNil u1 v1 v2) (ifNil u2 v1 v2)
ifNil∘ifNil VNil = refl
ifNil∘ifNil (VCons _ _) = refl
ifNil∘ifNil VBottom = refl

-- evalT

evalT : (t : Trm) (v : Val) →  Val

evalT [] v = VNil
evalT (t1 ∷ t2) v = VCons (evalT t1 v) (evalT t2 v)
evalT (Sel sel) v = evalSel v sel
evalT Id v = v
evalT (t1 $$ t2) v = evalT t1 (evalT t2 v)
evalT (IfNil t0 t1 t2) v =
  ifNil (evalT t0 v) (evalT t1 v) (evalT t2 v) 
evalT Bottom v = VBottom

-- sel2trm

sel2trm : (t : Trm) → (sel : Selector) → Trm
sel2trm Id sel = Sel sel
sel2trm t sel = Sel sel $$ t

-- sels2trm

sels2trm : (sels : List Selector) → Trm
sels2trm sels = foldl sel2trm Id sels

-- evalT∘sel2trm

evalT∘sel2trm : ∀ t sel v → evalT (sel2trm t sel) v ≡ evalSel (evalT t v) sel
evalT∘sel2trm [] sel v = refl
evalT∘sel2trm (t1 ∷ t2) sel v = refl
evalT∘sel2trm (Sel sel) sel' v = refl
evalT∘sel2trm Id sel v = refl
evalT∘sel2trm (t1 $$ t2) sel v = refl
evalT∘sel2trm (IfNil t0 t1 t2) sel v = refl
evalT∘sel2trm Bottom sel v = refl

-- evalT∘foldr

evalT∘foldr : ∀ rsels v →
  evalT (foldr (flip sel2trm) Id rsels) v ≡
  foldr (flip evalSel) v rsels

evalT∘foldr [] v = refl

evalT∘foldr (sel ∷ rsels) v =
  begin
    evalT (foldr (flip sel2trm) Id (sel ∷ rsels)) v
      ≡⟨ refl ⟩
    evalT (sel2trm (foldr (flip sel2trm) Id rsels) sel) v
      ≡⟨ evalT∘sel2trm (foldr (flip sel2trm) Id rsels) sel v ⟩
    evalT (Sel sel $$ foldr (flip sel2trm) Id rsels) v
      ≡⟨ refl ⟩
    evalSel (evalT (foldr (flip sel2trm) Id rsels) v) sel
      ≡⟨ cong (flip evalSel sel) (evalT∘foldr rsels v) ⟩
    evalSel (foldr (flip evalSel) v rsels) sel
      ≡⟨ refl ⟩
    foldr (flip evalSel) v (sel ∷ rsels)
  ∎

-- evalT∘sels2trm

evalT∘sels2trm : ∀ sels v →
  evalT (sels2trm sels) v ≡ evalSels v sels

evalT∘sels2trm sels v =
  begin
    evalT (sels2trm sels) v
      ≡⟨ refl ⟩
    evalT (foldl sel2trm Id sels) v
      ≡⟨ cong (flip evalT v) (foldl⇒foldr-reverse sel2trm Id sels) ⟩
    evalT (foldr (flip sel2trm) Id (reverse sels)) v
      ≡⟨ evalT∘foldr (foldl (λ sels' sel → sel ∷ sels') [] sels) v ⟩
    foldr (flip evalSel) v (reverse sels)
      ≡⟨ sym (foldl⇒foldr-reverse evalSel v sels) ⟩
    foldl evalSel v sels
      ≡⟨ sym $ evalSelsIsFoldl v sels ⟩
    evalSels v sels
  ∎

-- evalSels-VBottom

evalSels-VBottom : ∀ (sels : List Selector) →
  evalSels VBottom sels ≡ VBottom

evalSels-VBottom [] = refl
evalSels-VBottom (sel ∷ sels) = evalSels-VBottom sels

-- evalSels∘ifNil

evalSels∘ifNil : ∀ v0 {v1 v2} (sels : List Selector) →
  evalSels (ifNil v0 v1 v2) sels ≡
    ifNil v0 (evalSels v1 sels) (evalSels v2 sels)

evalSels∘ifNil v0 {v1} {v2} sels =
  ifNil-distr (flip evalSels sels) (evalSels-VBottom sels) v0

-- evalSel∘ifNil

evalSel∘ifNil : ∀ v0 {v1 v2} (sel : Selector) →
  evalSel (ifNil v0 v1 v2) sel ≡
    ifNil v0 (evalSel v1 sel) (evalSel v2 sel)

evalSel∘ifNil v0 {v1} {v2} sel = evalSels∘ifNil v0 (sel ∷ [])


-- evalSels∘++

evalSels∘++ : ∀ (v : Val) (sels1 sels2 : List Selector) →
  evalSels v (sels1 ++ sels2) ≡ evalSels (evalSels v sels1) sels2

evalSels∘++ v [] sels2 = refl
evalSels∘++ v (sel ∷ xs) sels2 =
  evalSels∘++ (evalSel v sel) xs sels2

--
-- Normalization of simple expressions
--

-- NTrm

data NTrm : Set where
  NNil    : NTrm 
  NCons   : (nt1 : NTrm) → (nt2 : NTrm) → NTrm 
  NSelCmp : (sels : List Selector) → NTrm
  NIfNil  : (sels : List Selector) → (nt1 : NTrm) → (nt2 : NTrm) → NTrm
  NBottom : NTrm

-- ntrm2trm

ntrm2trm : (nt : NTrm) → Trm

ntrm2trm NNil = []
ntrm2trm (NCons nt1 nt2) = ntrm2trm nt1 ∷ ntrm2trm nt2
ntrm2trm (NSelCmp sels) = sels2trm sels
ntrm2trm (NIfNil sels nt1 nt2) =
  IfNil (sels2trm sels) (ntrm2trm nt1) (ntrm2trm nt2)
ntrm2trm NBottom = Bottom

-- evalNT

evalNT : (nt : NTrm) (v : Val) → Val
evalNT nt v = evalT (ntrm2trm nt) v

-- normSelNCmp

normSelNCmp : (nt : NTrm) (sel : Selector) → NTrm

normSelNCmp NNil sel = NBottom
normSelNCmp (NCons nt1 nt2) HD = nt1
normSelNCmp (NCons nt1 nt2) TL = nt2
normSelNCmp (NSelCmp sels) sel = NSelCmp (sels ++ [ sel ])
normSelNCmp (NIfNil sels nt1 nt2) sel =
  NIfNil sels (normSelNCmp nt1 sel) (normSelNCmp nt2 sel)
normSelNCmp NBottom sel = NBottom

-- evalNT∘normSelNCmp

evalNT∘normSelNCmp : (nt : NTrm) (sel : Selector) (v : Val) →
  evalNT (normSelNCmp nt sel) v ≡ evalSel (evalNT nt v) sel

evalNT∘normSelNCmp NNil sel v = refl
evalNT∘normSelNCmp (NCons nt1 nt2) HD v = refl
evalNT∘normSelNCmp (NCons nt1 nt2) TL v = refl

evalNT∘normSelNCmp (NSelCmp sels) sel v =
  begin
    evalNT (normSelNCmp (NSelCmp sels) sel) v
      ≡⟨ refl ⟩
    evalNT (NSelCmp (sels ++ [ sel ])) v
      ≡⟨ refl ⟩
    evalT (ntrm2trm (NSelCmp (sels ++ [ sel ]))) v
      ≡⟨ refl ⟩
    evalT (sels2trm (sels ++ [ sel ])) v
      ≡⟨ evalT∘sels2trm (sels ++ [ sel ]) v ⟩
    evalSels v (sels ++ [ sel ])
      ≡⟨ evalSels∘++ v sels [ sel ] ⟩
    evalSels (evalSels v sels) [ sel ]
      ≡⟨ refl ⟩
    evalSel (evalSels v sels) sel
      ≡⟨ sym (cong (flip evalSel sel) (evalT∘sels2trm sels v)) ⟩
    evalSel (evalT (sels2trm sels) v) sel
      ≡⟨ refl ⟩
    evalSel (evalT (ntrm2trm (NSelCmp sels)) v) sel
      ≡⟨ refl ⟩
    evalSel (evalNT (NSelCmp sels) v) sel
  ∎

evalNT∘normSelNCmp (NIfNil sels nt1 nt2) sel v =
  begin
    evalNT (normSelNCmp (NIfNil sels nt1 nt2) sel) v
      ≡⟨ refl ⟩
    ifNil (evalT (sels2trm sels) v)
          (evalNT (normSelNCmp nt1 sel) v)
          (evalNT (normSelNCmp nt2 sel) v)
      ≡⟨ cong₂ (ifNil (evalT (sels2trm sels) v))
               (evalNT∘normSelNCmp nt1 sel v)
               (evalNT∘normSelNCmp nt2 sel v) ⟩
    ifNil (evalT (sels2trm sels) v)
          (evalSel (evalNT nt1 v) sel)
          (evalSel (evalNT nt2 v) sel)
      ≡⟨ sym $ evalSel∘ifNil (evalT (sels2trm sels) v) sel ⟩
    evalSel (ifNil (evalT (sels2trm sels) v) (evalNT nt1 v) (evalNT nt2 v)) sel
      ≡⟨ refl ⟩
    evalSel (evalNT (NIfNil sels nt1 nt2) v) sel
  ∎

evalNT∘normSelNCmp NBottom sel v = refl

-- normSelsNCmp

normSelsNCmp : (nt : NTrm) (sels : List Selector) → NTrm
normSelsNCmp nt sels =
  foldl normSelNCmp nt sels

-- normSelsNCmp-NBottom

normSelsNCmp-NBottom : ∀ sels → normSelsNCmp NBottom sels ≡ NBottom
normSelsNCmp-NBottom [] = refl
normSelsNCmp-NBottom (x ∷ xs) = normSelsNCmp-NBottom xs

-- evalNT∘normSelsNCmp

evalNT∘normSelsNCmp :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    evalNT (normSelsNCmp nt sels) v ≡
    evalSels (evalNT nt v) sels

evalNT∘normSelsNCmp nt [] v = refl

evalNT∘normSelsNCmp nt (sel ∷ sels) v =
  begin
    evalNT (normSelsNCmp nt (sel ∷ sels)) v
      ≡⟨ refl ⟩
    evalNT (normSelsNCmp (normSelNCmp nt sel) sels) v
      ≡⟨ refl ⟩
    evalNT (normSelsNCmp (normSelNCmp nt sel) sels) v
      ≡⟨ evalNT∘normSelsNCmp (normSelNCmp nt sel) sels v ⟩
    evalSels (evalNT (normSelNCmp nt sel) v) sels
      ≡⟨ cong (flip evalSels sels)
              (evalNT∘normSelNCmp nt sel v) ⟩
    evalSels (evalSel (evalNT nt v) sel) sels
      ≡⟨ refl ⟩
    evalSels (evalNT nt v) (sel ∷ sels)
  ∎

-- normSelsNCmp∘NSelCmp

normSelsNCmp∘NSelCmp : ∀ (sels1 sels2 : List Selector) →
  normSelsNCmp (NSelCmp sels1) sels2 ≡ NSelCmp (sels1 ++ sels2)

normSelsNCmp∘NSelCmp sels1 []
  rewrite ++-[] sels1
  = refl
normSelsNCmp∘NSelCmp sels1 (sel ∷ sels) = begin
  normSelsNCmp (NSelCmp sels1) (sel ∷ sels)
    ≡⟨ refl ⟩
  normSelsNCmp (NSelCmp (sels1 ++ sel ∷ [])) sels
    ≡⟨ normSelsNCmp∘NSelCmp (sels1 ++ sel ∷ []) sels ⟩
  NSelCmp ((sels1 ++ sel ∷ []) ++ sels)
    ≡⟨ cong NSelCmp (++-assoc sels1 (sel ∷ []) sels) ⟩
  NSelCmp (sels1 ++ (sel ∷ [] ++ sels))
    ≡⟨ refl ⟩
  NSelCmp (sels1 ++ sel ∷ sels)
  ∎

-- normNCmpSels

normNCmpSels : (nt : NTrm) (sels : List Selector) → NTrm

normNCmpSels NNil sels =
  NNil
normNCmpSels (NCons nt1 nt2) sels =
  NCons (normNCmpSels nt1 sels) (normNCmpSels nt2 sels)
normNCmpSels (NSelCmp sels2) sels =
  NSelCmp (sels ++ sels2)
normNCmpSels (NIfNil sels2 nt1 nt2) sels =
  NIfNil (sels ++ sels2) (normNCmpSels nt1 sels) (normNCmpSels nt2 sels)
normNCmpSels NBottom sels =
  NBottom

-- evalNT∘normNCmpSels

evalNT∘normNCmpSels :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    evalNT (normNCmpSels nt sels) v ≡ evalNT nt (evalSels v sels)

evalNT∘normNCmpSels NNil sels v = refl

evalNT∘normNCmpSels (NCons nt1 nt2) sels v
  rewrite evalNT∘normNCmpSels nt1 sels v
        | evalNT∘normNCmpSels nt2 sels v = refl

evalNT∘normNCmpSels (NSelCmp sels0) sels v =
  begin
    evalNT (normNCmpSels (NSelCmp sels0) sels) v
      ≡⟨ refl ⟩
    evalT (sels2trm (sels ++ sels0)) v
      ≡⟨ evalT∘sels2trm (sels ++ sels0) v ⟩
    evalSels v (sels ++ sels0)
      ≡⟨ evalSels∘++ v sels sels0 ⟩
    evalSels (evalSels v sels) sels0
      ≡⟨ sym (evalT∘sels2trm sels0 (evalSels v sels)) ⟩
    evalT (sels2trm sels0) (evalSels v sels)
      ≡⟨ refl ⟩
    evalNT (NSelCmp sels0) (evalSels v sels)
  ∎

evalNT∘normNCmpSels (NIfNil sels0 nt1 nt2) sels v
  rewrite evalT∘sels2trm (sels ++ sels0) v
        | evalT∘sels2trm sels0 (evalSels v sels)
        | evalSels∘++ v sels sels0
  = cong₂ (ifNil (evalSels (evalSels v sels) sels0))
          (evalNT∘normNCmpSels nt1 sels v)
          (evalNT∘normNCmpSels nt2 sels v)

evalNT∘normNCmpSels NBottom sels v = refl

-- normNCmpSels∘++

normNCmpSels∘++ : (nt : NTrm) (sels1 sels2 : List Selector) →
  normNCmpSels nt (sels1 ++ sels2) ≡
  normNCmpSels (normNCmpSels nt sels2) sels1

normNCmpSels∘++ NNil sels1 sels2 = refl
normNCmpSels∘++ (NCons nt1 nt2) sels1 sels2
{-
  rewrite normNCmpSels∘++ nt2 sels1 sels2
        | normNCmpSels∘++ nt1 sels1 sels2
  = refl
-}
  =
  begin
    NCons (normNCmpSels nt1 (sels1 ++ sels2))
          (normNCmpSels nt2 (sels1 ++ sels2))
    ≡⟨ cong (NCons (normNCmpSels nt1 (sels1 ++ sels2)))
            (normNCmpSels∘++ nt2 sels1 sels2) ⟩
    NCons (normNCmpSels nt1 (sels1 ++ sels2))
          (normNCmpSels (normNCmpSels nt2 sels2) sels1)
    ≡⟨ cong (λ z → NCons z (normNCmpSels (normNCmpSels nt2 sels2) sels1))
            (normNCmpSels∘++ nt1 sels1 sels2) ⟩
    NCons (normNCmpSels (normNCmpSels nt1 sels2) sels1)
           (normNCmpSels (normNCmpSels nt2 sels2) sels1)
  ∎

normNCmpSels∘++ (NSelCmp sels) sels1 sels2
  rewrite ++-assoc sels1 sels2 sels
  =  refl

normNCmpSels∘++ (NIfNil sels nt1 nt2) sels1 sels2
  rewrite ++-assoc sels1 sels2 sels
        | normNCmpSels∘++ nt1 sels1 sels2
        | normNCmpSels∘++ nt2 sels1 sels2
  = refl

normNCmpSels∘++  NBottom sels1 sels2 = refl

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

-- evalNT∘normNIf

evalNT∘normNIf : ∀ (nt1 nt2 nt3 : NTrm) (v : Val) →
  evalNT (normNIf nt1 nt2 nt3) v ≡
    ifNil (evalNT nt1 v) (evalNT nt2 v) (evalNT nt3 v)

evalNT∘normNIf NNil nt2 nt3 v = refl
evalNT∘normNIf (NCons nt' nt'') nt2 nt3 v = refl
evalNT∘normNIf (NSelCmp sels) nt2 nt3 v
  with evalT (sels2trm sels) v
... | VNil = refl
... | VCons v1 v2 = refl
... | VBottom = refl
evalNT∘normNIf (NIfNil sels nt' nt'') nt2 nt3 v
  with evalT (sels2trm sels) v
... | VNil        rewrite evalNT∘normNIf nt'  nt2 nt3 v = refl
... | VCons v1 v2 rewrite evalNT∘normNIf nt'' nt2 nt3 v = refl
... | VBottom = refl
evalNT∘normNIf NBottom nt2 nt3 v = refl

-- normNCmp

normNCmp : NTrm → NTrm → NTrm

normNCmp NNil nt2 =
  NNil

normNCmp (NCons nt' nt'') nt2 =
  NCons (normNCmp nt' nt2) (normNCmp nt'' nt2)

normNCmp (NSelCmp sels) nt2 =
  normSelsNCmp nt2 sels

normNCmp (NIfNil sels nt' nt'') (NSelCmp sels2) =
  NIfNil (sels2 ++ sels) (normNCmpSels nt' sels2) (normNCmpSels nt'' sels2)

normNCmp (NIfNil sels nt' nt'') (NIfNil sels2 nt2' nt2'') =
  NIfNil sels2 (normNCmp (NIfNil sels nt' nt'') nt2')
               (normNCmp (NIfNil sels nt' nt'') nt2'')

normNCmp (NIfNil sels nt' nt'') nt2 =
  normNIf (normSelsNCmp nt2 sels) (normNCmp nt' nt2) (normNCmp nt'' nt2)

normNCmp NBottom nt2 =
  NBottom

-- normNCmp∘NIfNil

normNCmp∘NIfNil : (sels1 sels2 : List Selector) →
  (nt1-1 nt1-2 nt2-1 nt2-2 : NTrm) →
  let nt1 = NIfNil sels1 nt1-1 nt1-2 in 
  normNCmp nt1 (NIfNil sels2 nt2-1 nt2-2)
    ≡ NIfNil sels2 (normNCmp nt1 nt2-1) (normNCmp nt1 nt2-2)

normNCmp∘NIfNil sels1 sels2 nt1-1 nt1-2 nt2-1 nt2-2 = refl

--
-- evalNT∘normNCmp
--

evalNT∘normNCmp : (nt1 nt2 : NTrm) (v : Val) →
  evalNT (normNCmp nt1 nt2) v ≡ evalNT nt1 (evalNT nt2 v)

evalNT∘normNCmp NNil nt2 v =
  refl

evalNT∘normNCmp (NCons nt' nt'') nt2 v
  rewrite evalNT∘normNCmp nt' nt2 v
        | evalNT∘normNCmp nt'' nt2 v
  = refl

evalNT∘normNCmp (NSelCmp sels) nt2 v =
  begin
    evalNT (normNCmp (NSelCmp sels) nt2) v
      ≡⟨ refl ⟩
    evalNT (normSelsNCmp nt2 sels) v
      ≡⟨ evalNT∘normSelsNCmp nt2 sels v ⟩
    evalSels (evalT (ntrm2trm nt2) v) sels
      ≡⟨ sym (evalT∘sels2trm sels (evalT (ntrm2trm nt2) v)) ⟩
    evalT (sels2trm sels) (evalT (ntrm2trm nt2) v)
      ≡⟨ refl ⟩
    evalNT (NSelCmp sels) (evalNT nt2 v)
  ∎

evalNT∘normNCmp (NIfNil sels nt' nt'') nt2 v =
  begin
    evalNT (normNCmp (NIfNil sels nt' nt'') nt2) v
      ≡⟨ helper nt2 ⟩
    ifNil (evalNT (normSelsNCmp nt2 sels) v)
          (evalNT (normNCmp nt' nt2) v) (evalNT (normNCmp nt'' nt2) v)
      ≡⟨ ifNil-cong (evalNT∘normSelsNCmp nt2 sels v) refl refl ⟩
    ifNil (evalSels (evalNT nt2 v) sels)
          (evalNT (normNCmp nt' nt2) v) (evalNT (normNCmp nt'' nt2) v)
      ≡⟨ ifNil-cong (sym $
           evalT∘sels2trm sels (evalT (ntrm2trm nt2) v))
           (evalNT∘normNCmp nt' nt2 v)
           (evalNT∘normNCmp nt'' nt2 v) ⟩
    ifNil (evalT (sels2trm sels) (evalNT nt2 v))
          (evalNT nt' (evalNT nt2 v)) (evalNT nt''(evalNT nt2 v))
      ≡⟨ refl ⟩
    evalNT (NIfNil sels nt' nt'') (evalNT nt2 v)
  ∎
  where
    helper : (nt2 : NTrm) →
      evalNT (normNCmp (NIfNil sels nt' nt'') nt2) v
      ≡
      ifNil (evalNT (normSelsNCmp nt2 sels) v)
            (evalNT (normNCmp nt' nt2) v) (evalNT (normNCmp nt'' nt2) v)

    helper (NSelCmp sels') = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') (NSelCmp sels')) v
        ≡⟨ refl ⟩
      ifNil (evalT (sels2trm (sels' ++ sels)) v)
            (evalNT (normNCmpSels nt' sels') v)
            (evalNT (normNCmpSels nt'' sels') v)
        ≡⟨ ifNil-cong
             (evalT∘sels2trm (sels' ++ sels) v)
             (evalNT∘normNCmpSels nt' sels' v)
             (evalNT∘normNCmpSels nt'' sels' v) ⟩
      ifNil (evalSels v (sels' ++ sels))
            (evalNT nt' (evalSels v sels'))
            (evalNT nt''(evalSels v sels'))
        ≡⟨ ifNil-cong
            (evalSels∘++ v sels' sels)
            (sym $ cong (evalT (ntrm2trm nt')) (evalT∘sels2trm sels' v))
            (sym $ cong (evalT (ntrm2trm nt'')) (evalT∘sels2trm sels' v)) ⟩
      ifNil (evalSels (evalSels v sels') sels)
            (evalNT nt' (evalNT (NSelCmp sels') v))
            (evalNT nt'' (evalNT (NSelCmp sels') v))
        ≡⟨ ifNil-cong
             (cong (flip evalSels sels) (sym (evalT∘sels2trm sels' v)))
             (sym $ evalNT∘normNCmp nt' (NSelCmp sels') v)
             (sym $ evalNT∘normNCmp nt'' (NSelCmp sels') v) ⟩
      ifNil (evalSels (evalT (sels2trm sels') v) sels)
            (evalNT (normNCmp nt' (NSelCmp sels')) v)
            (evalNT (normNCmp nt'' (NSelCmp sels')) v)
        ≡⟨ refl ⟩
      ifNil (evalSels (evalNT (NSelCmp sels') v) sels)
            (evalNT (normNCmp nt' (NSelCmp sels')) v)
            (evalNT (normNCmp nt'' (NSelCmp sels')) v)
        ≡⟨ ifNil-cong
             (sym (evalNT∘normSelsNCmp (NSelCmp sels') sels v))
             refl refl ⟩
      ifNil (evalNT (normSelsNCmp (NSelCmp sels') sels) v)
            (evalNT (normNCmp nt' (NSelCmp sels')) v)
            (evalNT (normNCmp nt'' (NSelCmp sels')) v)
      ∎

    helper (NIfNil sels' nt1 nt3) = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') (NIfNil sels' nt1 nt3)) v
        ≡⟨ cong (flip evalNT v)
                (normNCmp∘NIfNil sels sels' nt' nt'' nt1 nt3) ⟩
      evalNT (NIfNil sels'
        (normNCmp (NIfNil sels nt' nt'') nt1)
        (normNCmp (NIfNil sels nt' nt'') nt3)) v
        ≡⟨ refl ⟩
      ifNil (evalT (sels2trm sels') v)
        (evalNT (normNCmp (NIfNil sels nt' nt'') nt1) v)
        (evalNT (normNCmp (NIfNil sels nt' nt'') nt3) v)
        ≡⟨ ifNil-cong
             (evalT∘sels2trm sels' v)
             (evalNT∘normNCmp (NIfNil sels nt' nt'') nt1 v)
             (evalNT∘normNCmp (NIfNil sels nt' nt'') nt3 v) ⟩
      ifNil (evalSels v sels')
        (evalNT (NIfNil sels nt' nt'') (evalNT nt1 v))
        (evalNT (NIfNil sels nt' nt'') (evalNT nt3 v))
        ≡⟨ refl ⟩
      ifNil (evalSels v sels')
        (ifNil (evalT (sels2trm sels) (evalNT nt1 v))
               (evalNT nt' (evalNT nt1 v))
               (evalNT nt'' (evalNT nt1 v)))
        (ifNil (evalT (sels2trm sels) (evalNT nt3 v))
               (evalNT nt' (evalNT nt3 v))
               (evalNT nt'' (evalNT nt3 v)))
        ≡⟨ cong₂ (ifNil (evalSels v sels'))
                 (ifNil-cong (evalT∘sels2trm sels (evalNT nt1 v)) refl refl)
                 (ifNil-cong (evalT∘sels2trm sels (evalNT nt3 v)) refl refl) ⟩
      ifNil (evalSels v sels')
        (ifNil (evalSels (evalNT nt1 v) sels)
               (evalNT nt' (evalNT nt1 v))
               (evalNT nt'' (evalNT nt1 v)))
        (ifNil (evalSels (evalNT nt3 v) sels)
               (evalNT nt' (evalNT nt3 v))
               (evalNT nt'' (evalNT nt3 v)))
        ≡⟨ helper₂ (evalSels v sels')
                   (evalSels (evalNT nt1 v) sels)
                   (evalSels (evalNT nt3 v) sels)
                   (evalNT nt') (evalNT nt'')
                   (evalNT nt1 v) (evalNT nt3 v)
         ⟩
      ifNil (evalSels v sels')
            (ifNil (evalSels (evalNT nt1 v) sels)
                   (evalNT nt' (ifNil (evalSels v sels')
                                      (evalNT nt1 v) (evalNT nt3 v)))
                   (evalNT nt'' (ifNil (evalSels v sels')
                                       (evalNT nt1 v) (evalNT nt3 v))))
            (ifNil (evalSels (evalNT nt3 v) sels)
                   (evalNT nt' (ifNil (evalSels v sels')
                                      (evalNT nt1 v) (evalNT nt3 v)))
                   (evalNT nt'' (ifNil (evalSels v sels')
                                       (evalNT nt1 v) (evalNT nt3 v))))
        ≡⟨ sym $ ifNil∘ifNil (evalSels v sels') ⟩
      ifNil (ifNil (evalSels v sels')
                   (evalSels (evalNT nt1 v) sels)
                   (evalSels (evalNT nt3 v) sels))
            (evalNT nt' (ifNil (evalSels v sels')
                               (evalNT nt1 v) (evalNT nt3 v)))
            (evalNT nt'' (ifNil (evalSels v sels')
                                (evalNT nt1 v) (evalNT nt3 v)))
        ≡⟨ ifNil-cong (sym $ evalSels∘ifNil (evalSels v sels') sels) refl refl ⟩
      ifNil (evalSels (ifNil (evalSels v sels')
                             (evalNT nt1 v) (evalNT nt3 v)) sels)
            (evalNT nt' (ifNil (evalSels v sels')
                               (evalNT nt1 v) (evalNT nt3 v)))
            (evalNT nt'' (ifNil (evalSels v sels')
                                (evalNT nt1 v) (evalNT nt3 v)))
        ≡⟨ ifNil-cong
             (cong (flip evalSels sels)
                   (ifNil-cong (sym $ evalT∘sels2trm sels' v) refl refl))
             (cong (evalNT nt')
                   (ifNil-cong (sym $ evalT∘sels2trm sels' v) refl refl))
             (cong (evalNT nt'')
                   (ifNil-cong (sym $ evalT∘sels2trm sels' v) refl refl)) ⟩
      ifNil (evalSels (ifNil (evalT (sels2trm sels') v)
                             (evalNT nt1 v) (evalNT nt3 v)) sels)
            (evalNT nt' (ifNil (evalT (sels2trm sels') v)
                               (evalNT nt1 v) (evalNT nt3 v)))
            (evalNT nt'' (ifNil (evalT (sels2trm sels') v)
                                (evalNT nt1 v) (evalNT nt3 v)))
        ≡⟨ refl ⟩
      ifNil (evalSels (evalNT (NIfNil sels' nt1 nt3) v) sels)
            (evalNT nt' (evalNT (NIfNil sels' nt1 nt3) v))
            (evalNT nt'' (evalNT (NIfNil sels' nt1 nt3) v))
        ≡⟨ ifNil-cong
             (sym $ evalNT∘normSelsNCmp (NIfNil sels' nt1 nt3) sels v)
             (sym $ evalNT∘normNCmp nt' (NIfNil sels' nt1 nt3) v)
             (sym $ evalNT∘normNCmp nt'' (NIfNil sels' nt1 nt3) v) ⟩
      ifNil (evalNT (normSelsNCmp (NIfNil sels' nt1 nt3) sels) v)
            (evalNT (normNCmp nt' (NIfNil sels' nt1 nt3)) v)
            (evalNT (normNCmp nt'' (NIfNil sels' nt1 nt3)) v)
      ∎
      where
        helper₂ : ∀ w (u1 u3 : Val) (f1 f2 : Val → Val) (v1 v3 : Val) →
          ifNil w (ifNil u1 (f1 v1) (f2 v1))
                  (ifNil u3 (f1 v3) (f2 v3))
          ≡
          ifNil w (ifNil u1 (f1 (ifNil w v1 v3)) (f2 (ifNil w v1 v3)))
                  (ifNil u3 (f1 (ifNil w v1 v3)) (f2 (ifNil w v1 v3)))
        helper₂ VNil        u1 u3 f1 f2 v1 v3 = refl
        helper₂ (VCons _ _) u1 u3 f1 f2 v1 v3 = refl
        helper₂ VBottom     u1 u3 f1 f2 v1 v3 = refl

    helper NNil = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') NNil) v
        ≡⟨ refl ⟩
      evalNT (normNIf (normSelsNCmp NNil sels)
                      (normNCmp nt' NNil) (normNCmp nt'' NNil)) v
        ≡⟨ evalNT∘normNIf
             (normSelsNCmp NNil sels)
             (normNCmp nt' NNil) (normNCmp nt'' NNil) v ⟩
      ifNil (evalNT (normSelsNCmp NNil sels) v)
            (evalNT (normNCmp nt' NNil) v) (evalNT (normNCmp nt'' NNil) v)
      ∎

    helper (NCons nt1 nt3) = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') (NCons nt1 nt3)) v
        ≡⟨ refl ⟩
      evalNT (normNIf (normSelsNCmp (NCons nt1 nt3) sels)
                      (normNCmp nt' (NCons nt1 nt3))
                      (normNCmp nt'' (NCons nt1 nt3))) v
        ≡⟨ evalNT∘normNIf
             (normSelsNCmp (NCons nt1 nt3) sels)
             (normNCmp nt' (NCons nt1 nt3)) (normNCmp nt'' (NCons nt1 nt3)) v ⟩
      ifNil (evalNT (normSelsNCmp (NCons nt1 nt3) sels) v)
            (evalNT (normNCmp nt' (NCons nt1 nt3)) v)
            (evalNT (normNCmp nt'' (NCons nt1 nt3)) v)
      ∎

    helper NBottom = begin
      evalNT (normNCmp (NIfNil sels nt' nt'') NBottom) v
        ≡⟨ refl ⟩
      evalNT (normNIf (normSelsNCmp NBottom sels)
                      (normNCmp nt' NBottom) (normNCmp nt'' NBottom)) v
        ≡⟨ evalNT∘normNIf (normSelsNCmp NBottom sels)
                          (normNCmp nt' NBottom) (normNCmp nt'' NBottom) v ⟩
      ifNil (evalNT (normSelsNCmp NBottom sels) v)
            (evalNT (normNCmp nt' NBottom) v)
            (evalNT (normNCmp nt'' NBottom) v)
      ∎

evalNT∘normNCmp NBottom nt2 v =
  refl

-- normConv

normConv : (t : Trm) → NTrm

normConv [] = NNil
normConv (t1 ∷ t2) = NCons (normConv t1) (normConv t2)
normConv (Sel sel) = NSelCmp [ sel ]
normConv Id = NSelCmp []
normConv (t1 $$ t2) = normNCmp (normConv t1) (normConv t2)
normConv (IfNil t0 t1 t2) = normNIf (normConv t0) (normConv t1) (normConv t2)
normConv Bottom = NBottom

--
-- The main theorem establishing the correctness of normalization.
--

-- evalNT∘normConv

evalNT∘normConv : (t : Trm) (v : Val) →
  evalNT (normConv t) v ≡ evalT t v

evalNT∘normConv [] v =
  refl
evalNT∘normConv (t1 ∷ t2) v
  rewrite evalNT∘normConv t1 v | evalNT∘normConv t2 v
  = refl
evalNT∘normConv (Sel sel) v =
  refl
evalNT∘normConv Id v =
  refl
evalNT∘normConv (t1 $$ t2) v = begin
  evalNT (normConv (t1 $$ t2)) v
    ≡⟨ refl ⟩
  evalNT (normNCmp (normConv t1) (normConv t2)) v
    ≡⟨ evalNT∘normNCmp (normConv t1) (normConv t2) v ⟩
  evalNT (normConv t1) (evalNT (normConv t2) v)
    ≡⟨ cong (evalNT (normConv t1)) (evalNT∘normConv t2 v) ⟩
  evalNT (normConv t1) (evalT t2 v)
    ≡⟨ evalNT∘normConv t1 (evalT t2 v) ⟩
  evalT t1 (evalT t2 v)
    ≡⟨ refl ⟩
  evalT (t1 $$ t2) v
  ∎
evalNT∘normConv (IfNil t0 t1 t2) v = begin
  evalNT (normConv (IfNil t0 t1 t2)) v
    ≡⟨ refl ⟩
  evalNT (normNIf (normConv t0) (normConv t1) (normConv t2)) v
    ≡⟨ evalNT∘normNIf (normConv t0) (normConv t1) (normConv t2) v ⟩
  ifNil (evalNT (normConv t0) v)
        (evalNT (normConv t1) v) (evalNT (normConv t2) v)
    ≡⟨ ifNil-cong (evalNT∘normConv t0 v)
                  (evalNT∘normConv t1 v) (evalNT∘normConv t2 v) ⟩
  ifNil (evalT t0 v) (evalT t1 v) (evalT t2 v)
    ≡⟨ refl ⟩
  evalT (IfNil t0 t1 t2) v
  ∎
evalNT∘normConv Bottom v =
  refl

--
-- Emulating substitutions
--

-- replaceAt

replaceAt : (sels : List Selector) (t t′ : NTrm) → NTrm

replaceAt [] t t′ = t′
replaceAt (HD ∷ sels) t t′ =
  NCons (replaceAt sels (normSelNCmp t HD) t′) (normSelNCmp t TL)
replaceAt (TL ∷ sels) t t′ =
  NCons (normSelNCmp t HD) (replaceAt sels (normSelNCmp t TL) t′)

-- normSelsNCmp∘replaceAt

normSelsNCmp∘replaceAt : (sels : List Selector) (t t′ : NTrm) →
  normSelsNCmp (replaceAt sels t t′) sels ≡ t′

normSelsNCmp∘replaceAt [] t t′ = refl
normSelsNCmp∘replaceAt (HD ∷ sels) t t′ = begin
  normSelsNCmp (replaceAt (HD ∷ sels) t t′) (HD ∷ sels)
    ≡⟨ refl ⟩
  normSelsNCmp (replaceAt sels (normSelNCmp t HD) t′) sels
    ≡⟨ normSelsNCmp∘replaceAt sels (normSelNCmp t HD) t′ ⟩
  t′
  ∎
normSelsNCmp∘replaceAt (TL ∷ sels) t t′ = begin
  normSelsNCmp (replaceAt (TL ∷ sels) t t′) (TL ∷ sels)
    ≡⟨ refl ⟩
  normSelsNCmp (replaceAt sels (normSelNCmp t TL) t′) sels
    ≡⟨ normSelsNCmp∘replaceAt sels (normSelNCmp t TL) t′ ⟩
  t′
  ∎

-- replaceAt∘++

replaceAt∘++ : ∀ (sels1 sels2 : List Selector) (nt nt′ : NTrm) →
  replaceAt (sels1 ++ sels2) nt nt′
  ≡
  replaceAt sels1 nt (replaceAt sels2 (normSelsNCmp nt sels1) nt′)

replaceAt∘++ [] sels2 nt nt′ = refl
replaceAt∘++ (HD ∷ sels1) sels2 nt nt′ = begin
  replaceAt ((HD ∷ sels1) ++ sels2) nt nt′
    ≡⟨ refl ⟩
  NCons (replaceAt (sels1 ++ sels2) (normSelNCmp nt HD) nt′)
        (normSelNCmp nt TL)
    ≡⟨ cong (flip NCons (normSelNCmp nt TL))
            (replaceAt∘++ sels1 sels2 (normSelNCmp nt HD) nt′) ⟩
  NCons (replaceAt sels1 (normSelNCmp nt HD)
            (replaceAt sels2 (normSelsNCmp (normSelNCmp nt HD) sels1) nt′))
        (normSelNCmp nt TL)
    ≡⟨ refl ⟩
  replaceAt (HD ∷ sels1) nt
            (replaceAt sels2 (normSelsNCmp nt (HD ∷ sels1)) nt′)
  ∎
replaceAt∘++ (TL ∷ sels1) sels2 nt nt′ =
  cong (NCons (normSelNCmp nt HD))
       (replaceAt∘++ sels1 sels2 (normSelNCmp nt TL) nt′)

-- _≟Sel_

_≟Sel_ : (sel1 sel2 : Selector) → Dec (sel1 ≡ sel2)

HD ≟Sel HD = yes refl
HD ≟Sel TL = no (λ ())
TL ≟Sel HD = no (λ ())
TL ≟Sel TL = yes refl

-- commonPrefix

commonPrefix :
  ∀ {ℓ} {A : Set ℓ} (eq : (u v : A) → Dec (u ≡ v)) (xs ys : List A) →
        List A × List A × List A

commonPrefix eq [] ys = [] , [] , ys
commonPrefix eq xs [] = [] , xs , []
commonPrefix eq (x ∷ xs) (y ∷ ys) with eq x y
... | no _  = [] , x ∷ xs , y ∷ ys
... | yes _ with commonPrefix eq xs ys
... | zs , xs′ , ys′  = y ∷ zs , xs′ , ys′

commonPrefix? :
  ∀ {ℓ} {A : Set ℓ} (eq : (u v : A) → Dec (u ≡ v)) (xs ys : List A) →
        ∃ λ ws → ∃₂ λ us vs → xs ≡ ws ++ us × ys ≡ ws ++ vs
commonPrefix? eq [] ys = [] , [] , ys , refl , refl
commonPrefix? eq xs [] = [] , xs , [] , refl , refl
commonPrefix? eq (x ∷ xs) (y ∷ ys) with eq x y
... | no _ = [] , x ∷ xs , y ∷ ys , refl , refl
... | yes _ with commonPrefix? eq xs ys
... | ws , us , vs , xs≡ws++us ,  ys≡ws++vs =
  [] , x ∷ xs , y ∷ ys , refl , refl

-- commonPrefix∘++

commonPrefix∘++ :
  ∀ {ℓ} {A : Set ℓ} (eq : (u v : A) → Dec (u ≡ v)) (xs ys : List A) →
    commonPrefix eq xs (xs ++ ys) ≡ xs , [] , ys

commonPrefix∘++ eq [] ys = refl
commonPrefix∘++ eq (x ∷ xs) ys with eq x x
... | no  x≢x = ⊥-elim (x≢x refl)
... | yes x≡x rewrite commonPrefix∘++ eq xs ys = refl

-- commonPrefix-[]

commonPrefix-[] :
  ∀ {ℓ} {A : Set ℓ} (eq : (u v : A) → Dec (u ≡ v)) (xs : List A) →
    commonPrefix eq xs [] ≡ [] , xs , []
commonPrefix-[] eq [] = refl
commonPrefix-[] eq (x ∷ xs) = refl

-- normSelsNCmp∘ReplaceAt

normSelsNCmp∘ReplaceAt′ :
  ∀ (ws us vs : List Selector) (nt nt′ : NTrm) →
    normSelsNCmp (replaceAt (ws ++ vs) nt nt′) (ws ++ us)
      ≡ normSelsNCmp (replaceAt vs (normSelsNCmp nt ws) nt′) us

normSelsNCmp∘ReplaceAt′ [] us vs nt nt′ = refl
normSelsNCmp∘ReplaceAt′ (HD ∷ ws) us vs nt nt′ =
  normSelsNCmp∘ReplaceAt′ ws us vs (normSelNCmp nt HD) nt′
normSelsNCmp∘ReplaceAt′ (TL ∷ ws) us vs nt nt′ =
  normSelsNCmp∘ReplaceAt′ ws us vs (normSelNCmp nt TL) nt′

normSelsNCmp∘ReplaceAt :
  ∀ (sels1 sels2 : List Selector) (nt nt′ : NTrm) →
    let cp = commonPrefix? _≟Sel_ sels1 sels2
        ws = proj₁ cp
        us = proj₁ (proj₂ cp)
        vs = proj₁ (proj₂ (proj₂ cp))
    in normSelsNCmp (replaceAt sels2 nt nt′) sels1
       ≡ normSelsNCmp (replaceAt vs (normSelsNCmp nt ws) nt′) us

normSelsNCmp∘ReplaceAt sels1 sels2 nt nt′ with commonPrefix? _≟Sel_ sels1 sels2
... | ws , us , vs , sels1≡ws++us , sels2≡ws++vs
  rewrite sels1≡ws++us | sels2≡ws++vs =
  normSelsNCmp∘ReplaceAt′ ws us vs nt nt′

-- replaceAt∘NSelCmp

replaceAt∘NSelCmp : (sels1 sels2 : List Selector) (nt : NTrm) →
  replaceAt sels1 (NSelCmp sels2) nt 
    ≡ normSelsNCmp (replaceAt (sels2 ++ sels1) (NSelCmp []) nt) sels2

replaceAt∘NSelCmp sels1 sels2 nt =
  begin
    replaceAt sels1 (NSelCmp sels2) nt
      ≡⟨ refl ⟩
    normSelsNCmp (replaceAt sels1 (NSelCmp sels2) nt) []
      ≡⟨ cong (λ z → normSelsNCmp (replaceAt sels1 z nt) [])
              (sym $ normSelsNCmp∘NSelCmp [] sels2) ⟩
    normSelsNCmp (replaceAt sels1 (normSelsNCmp (NSelCmp []) sels2) nt) []
      ≡⟨ sym $ normSelsNCmp∘ReplaceAt [] sels1
                                      (normSelsNCmp (NSelCmp []) sels2)
                                      nt ⟩
    replaceAt sels1 (normSelsNCmp (NSelCmp []) sels2) nt
      ≡⟨ sym $ normSelsNCmp∘ReplaceAt′ sels2 [] sels1 (NSelCmp []) nt ⟩
    normSelsNCmp (replaceAt (sels2 ++ sels1) (NSelCmp []) nt) (sels2 ++ [])
      ≡⟨ cong (normSelsNCmp (replaceAt (sels2 ++ sels1) (NSelCmp []) nt))
              (++-[] sels2) ⟩
    normSelsNCmp (replaceAt (sels2 ++ sels1) (NSelCmp []) nt) sels2
  ∎

--
