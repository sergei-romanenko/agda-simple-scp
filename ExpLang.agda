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
  VCons : (v1 v2 : Val) → Val
  VBottom : Val 

data Selector : Set where
  HD : Selector
  TL : Selector

data Trm : Set where
  []    : Trm
  _∷_   : (t1 t2 : Trm) → Trm 
  Sel   : (sel : Selector) → Trm
  Id    : Trm
  _$$_  : (t1 t2 : Trm) → Trm
  IfNil : (t0 t1 t2 : Trm) → Trm
  ↯     : Trm

-- Hd Tl

Hd = Sel HD
Tl = Sel TL

-- _!_

infixl 4 _!_ _!!_

_!_ : (v : Val) → (sel : Selector) → Val

VNil ! sel = VBottom
VCons v1 v2 ! HD = v1
VCons v1 v2 ! TL = v2
VBottom ! sel = VBottom

-- _!!_

_!!_ : (v : Val) (sels : List Selector) → Val

v !! [] = v
v !! (x ∷ xs) = (v ! x) !! xs

-- !!IsFoldl

!!IsFoldl : ∀ v sels →
  v !! sels ≡ foldl _!_ v sels
!!IsFoldl v [] = refl
!!IsFoldl v (x ∷ xs) = !!IsFoldl (v ! x) xs

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

-- ⟦_⟧

⟦_⟧ : (t : Trm) (v : Val) →  Val

⟦ [] ⟧ v = VNil
⟦ t1 ∷ t2 ⟧ v = VCons (⟦ t1 ⟧ v) (⟦ t2 ⟧ v)
⟦ Sel sel ⟧ v = v ! sel
⟦ Id ⟧ v = v
⟦ t1 $$ t2 ⟧ v = ⟦ t1 ⟧ (⟦ t2 ⟧ v)
⟦ IfNil t0 t1 t2 ⟧ v =
  ifNil (⟦ t0 ⟧ v) (⟦ t1 ⟧ v) (⟦ t2 ⟧ v) 
⟦ Bottom ⟧ v = VBottom

-- sel2trm

sel2trm : (t : Trm) → (sel : Selector) → Trm
sel2trm Id sel = Sel sel
sel2trm t sel = Sel sel $$ t

-- sels2trm

sels2trm : (sels : List Selector) → Trm
sels2trm sels = foldl sel2trm Id sels

-- ⟦⟧∘sel2trm

⟦⟧∘sel2trm : ∀ t sel v → ⟦ sel2trm t sel ⟧ v ≡ ⟦ t ⟧ v ! sel
⟦⟧∘sel2trm [] sel v = refl
⟦⟧∘sel2trm (t1 ∷ t2) sel v = refl
⟦⟧∘sel2trm (Sel sel) sel' v = refl
⟦⟧∘sel2trm Id sel v = refl
⟦⟧∘sel2trm (t1 $$ t2) sel v = refl
⟦⟧∘sel2trm (IfNil t0 t1 t2) sel v = refl
⟦⟧∘sel2trm ↯ sel v = refl

-- ⟦⟧∘foldr

⟦⟧∘foldr : ∀ rsels v →
  ⟦ foldr (flip sel2trm) Id rsels ⟧ v ≡
  foldr (flip _!_) v rsels

⟦⟧∘foldr [] v = refl

⟦⟧∘foldr (sel ∷ rsels) v =
  begin
    ⟦ foldr (flip sel2trm) Id (sel ∷ rsels) ⟧ v
      ≡⟨ refl ⟩
    ⟦ sel2trm (foldr (flip sel2trm) Id rsels) sel ⟧ v
      ≡⟨ ⟦⟧∘sel2trm (foldr (flip sel2trm) Id rsels) sel v ⟩
    ⟦ Sel sel $$ foldr (flip sel2trm) Id rsels ⟧ v
      ≡⟨ refl ⟩
    ⟦ foldr (flip sel2trm) Id rsels ⟧ v ! sel
      ≡⟨ cong (flip _!_ sel) (⟦⟧∘foldr rsels v) ⟩
    (foldr (flip _!_) v rsels) ! sel
      ≡⟨ refl ⟩
    foldr (flip _!_) v (sel ∷ rsels)
  ∎

-- ⟦⟧∘sels2trm

⟦⟧∘sels2trm : ∀ sels v →
  ⟦ sels2trm sels ⟧ v ≡ v !! sels

⟦⟧∘sels2trm sels v =
  begin
    ⟦ sels2trm sels ⟧ v
      ≡⟨ refl ⟩
    ⟦ foldl sel2trm Id sels ⟧ v
      ≡⟨ cong (flip ⟦_⟧ v) (foldl⇒foldr-reverse sel2trm Id sels) ⟩
    ⟦ foldr (flip sel2trm) Id (reverse sels) ⟧ v
      ≡⟨ ⟦⟧∘foldr (foldl (flip _∷_) [] sels) v ⟩
    foldr (flip _!_) v (reverse sels)
      ≡⟨ sym (foldl⇒foldr-reverse _!_ v sels) ⟩
    foldl _!_ v sels
      ≡⟨ sym $ !!IsFoldl v sels ⟩
    v !! sels
  ∎

-- !!-VBottom

!!-VBottom : ∀ (sels : List Selector) →
  VBottom !! sels ≡ VBottom

!!-VBottom [] = refl
!!-VBottom (sel ∷ sels) = !!-VBottom sels

-- !!∘ifNil

!!∘ifNil : ∀ v0 {v1 v2} (sels : List Selector) →
  (ifNil v0 v1 v2) !! sels ≡
    ifNil v0 (v1 !! sels) (v2 !! sels)

!!∘ifNil v0 {v1} {v2} sels =
  ifNil-distr (flip _!!_ sels) (!!-VBottom sels) v0

-- evalSel∘ifNil

evalSel∘ifNil : ∀ v0 {v1 v2} (sel : Selector) →
  (ifNil v0 v1 v2) ! sel ≡
    ifNil v0 (v1 ! sel) (v2 ! sel)

evalSel∘ifNil v0 {v1} {v2} sel = !!∘ifNil v0 (sel ∷ [])

-- !!∘++

!!∘++ : ∀ (v : Val) (sels1 sels2 : List Selector) →
  v !! (sels1 ++ sels2) ≡ v !! sels1 !! sels2

!!∘++ v [] sels2 = refl
!!∘++ v (sel ∷ xs) sels2 =
  !!∘++ (v ! sel) xs sels2

--
-- Normalization of simple expressions
--

-- NTrm

infixr 5 _∷ⁿ_
--infixr 6 _$$_

data NTrm : Set where
  []ⁿ     : NTrm 
  _∷ⁿ_    : (nt1 nt2 : NTrm) → NTrm 
  NSelCmp : (sels : List Selector) → NTrm
  IfNilⁿ  : (sels : List Selector) → (nt1 nt2 : NTrm) → NTrm
  ↯ⁿ      : NTrm

-- ⌈_⌉ 

⌈_⌉ : (nt : NTrm) → Trm

⌈ []ⁿ ⌉ = []
⌈ nt1 ∷ⁿ nt2 ⌉ = ⌈ nt1 ⌉ ∷ ⌈ nt2 ⌉
⌈ NSelCmp sels ⌉ = sels2trm sels
⌈  IfNilⁿ sels nt1 nt2 ⌉ =
  IfNil (sels2trm sels) ⌈ nt1 ⌉ ⌈ nt2 ⌉
⌈ NBottom ⌉ = ↯

-- ⟦⌈_⌉⟧

⟦⌈_⌉⟧ : (nt : NTrm) (v : Val) → Val
⟦⌈ nt ⌉⟧ v = ⟦ ⌈ nt ⌉ ⟧ v

-- normSelNCmp

normSelNCmp : (nt : NTrm) (sel : Selector) → NTrm

normSelNCmp []ⁿ sel = ↯ⁿ
normSelNCmp (nt1 ∷ⁿ nt2) HD = nt1
normSelNCmp (nt1 ∷ⁿ nt2) TL = nt2
normSelNCmp (NSelCmp sels) sel = NSelCmp (sels ++ [ sel ])
normSelNCmp (IfNilⁿ sels nt1 nt2) sel =
  IfNilⁿ sels (normSelNCmp nt1 sel) (normSelNCmp nt2 sel)
normSelNCmp ↯ⁿ sel = ↯ⁿ

-- ⟦⌈⌉⟧∘normSelNCmp

⟦⌈⌉⟧∘normSelNCmp : (nt : NTrm) (sel : Selector) (v : Val) →
  ⟦⌈ normSelNCmp nt sel ⌉⟧  v ≡ ⟦⌈ nt ⌉⟧ v ! sel

⟦⌈⌉⟧∘normSelNCmp []ⁿ sel v = refl
⟦⌈⌉⟧∘normSelNCmp (nt1 ∷ⁿ nt2) HD v = refl
⟦⌈⌉⟧∘normSelNCmp (nt1 ∷ⁿ nt2) TL v = refl

⟦⌈⌉⟧∘normSelNCmp (NSelCmp sels) sel v =
  begin
    ⟦⌈ normSelNCmp (NSelCmp sels) sel ⌉⟧ v
      ≡⟨ refl ⟩
    ⟦⌈ NSelCmp (sels ++ [ sel ]) ⌉⟧ v
      ≡⟨ refl ⟩
    ⟦ ⌈ NSelCmp (sels ++ [ sel ]) ⌉ ⟧ v
      ≡⟨ refl ⟩
    ⟦ sels2trm (sels ++ [ sel ]) ⟧ v
      ≡⟨ ⟦⟧∘sels2trm (sels ++ [ sel ]) v ⟩
    v !! (sels ++ [ sel ])
      ≡⟨ !!∘++ v sels [ sel ] ⟩
    v !! sels !! [ sel ]
      ≡⟨ refl ⟩
    v !! sels ! sel
      ≡⟨ sym (cong (flip _!_ sel) (⟦⟧∘sels2trm sels v)) ⟩
    ⟦ sels2trm sels ⟧ v ! sel
      ≡⟨ refl ⟩
    ⟦ ⌈ NSelCmp sels ⌉ ⟧ v ! sel
      ≡⟨ refl ⟩
    ⟦⌈ NSelCmp sels ⌉⟧ v ! sel
  ∎

⟦⌈⌉⟧∘normSelNCmp (IfNilⁿ sels nt1 nt2) sel v =
  begin
    ⟦⌈_⌉⟧ (normSelNCmp (IfNilⁿ sels nt1 nt2) sel) v
      ≡⟨ refl ⟩
    ifNil (⟦ sels2trm sels ⟧ v)
          (⟦⌈_⌉⟧ (normSelNCmp nt1 sel) v)
          (⟦⌈_⌉⟧ (normSelNCmp nt2 sel) v)
      ≡⟨ cong₂ (ifNil (⟦ sels2trm sels ⟧ v))
               (⟦⌈⌉⟧∘normSelNCmp nt1 sel v)
               (⟦⌈⌉⟧∘normSelNCmp nt2 sel v) ⟩
    ifNil (⟦ sels2trm sels ⟧  v)
          (⟦⌈ nt1 ⌉⟧ v ! sel)
          (⟦⌈ nt2 ⌉⟧ v ! sel)
      ≡⟨ sym $ evalSel∘ifNil (⟦ sels2trm sels ⟧  v) sel ⟩
    ifNil (⟦ (sels2trm sels) ⟧ v) (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt2 ⌉⟧ v) ! sel
      ≡⟨ refl ⟩
    ⟦⌈ IfNilⁿ sels nt1 nt2 ⌉⟧ v ! sel
  ∎

⟦⌈⌉⟧∘normSelNCmp ↯ⁿ sel v = refl

-- normSelsNCmp

normSelsNCmp : (nt : NTrm) (sels : List Selector) → NTrm
normSelsNCmp nt sels =
  foldl normSelNCmp nt sels

-- normSelsNCmp-↯ⁿ

normSelsNCmp-↯ⁿ : ∀ sels → normSelsNCmp ↯ⁿ sels ≡ ↯ⁿ
normSelsNCmp-↯ⁿ [] = refl
normSelsNCmp-↯ⁿ (x ∷ xs) = normSelsNCmp-↯ⁿ xs

-- ⟦⌈⌉⟧∘normSelsNCmp

⟦⌈⌉⟧∘normSelsNCmp :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    ⟦⌈ normSelsNCmp nt sels ⌉⟧ v ≡
    ⟦⌈ nt ⌉⟧ v !! sels

⟦⌈⌉⟧∘normSelsNCmp nt [] v = refl

⟦⌈⌉⟧∘normSelsNCmp nt (sel ∷ sels) v =
  begin
    ⟦⌈_⌉⟧ (normSelsNCmp nt (sel ∷ sels)) v
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (normSelsNCmp (normSelNCmp nt sel) sels) v
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (normSelsNCmp (normSelNCmp nt sel) sels) v
      ≡⟨ ⟦⌈⌉⟧∘normSelsNCmp (normSelNCmp nt sel) sels v ⟩
    ⟦⌈ normSelNCmp nt sel ⌉⟧ v !! sels
      ≡⟨ cong (flip _!!_ sels)
              (⟦⌈⌉⟧∘normSelNCmp nt sel v) ⟩
    ⟦⌈ nt ⌉⟧ v ! sel !! sels
      ≡⟨ refl ⟩
    ⟦⌈ nt ⌉⟧ v !! (sel ∷ sels)
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

normNCmpSels []ⁿ sels =
  []ⁿ
normNCmpSels (nt1 ∷ⁿ nt2) sels =
  normNCmpSels nt1 sels ∷ⁿ normNCmpSels nt2 sels
normNCmpSels (NSelCmp sels2) sels =
  NSelCmp (sels ++ sels2)
normNCmpSels (IfNilⁿ sels2 nt1 nt2) sels =
  IfNilⁿ (sels ++ sels2) (normNCmpSels nt1 sels) (normNCmpSels nt2 sels)
normNCmpSels ↯ⁿ sels =
  ↯ⁿ

-- ⟦⌈⌉⟧∘normNCmpSels

⟦⌈⌉⟧∘normNCmpSels :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    ⟦⌈ normNCmpSels nt sels ⌉⟧ v ≡ ⟦⌈_⌉⟧ nt (v !! sels)

⟦⌈⌉⟧∘normNCmpSels []ⁿ sels v = refl

⟦⌈⌉⟧∘normNCmpSels (nt1 ∷ⁿ nt2) sels v
  rewrite ⟦⌈⌉⟧∘normNCmpSels nt1 sels v
        | ⟦⌈⌉⟧∘normNCmpSels nt2 sels v = refl

⟦⌈⌉⟧∘normNCmpSels (NSelCmp sels0) sels v =
  begin
    ⟦⌈_⌉⟧ (normNCmpSels (NSelCmp sels0) sels) v
      ≡⟨ refl ⟩
    ⟦ sels2trm (sels ++ sels0) ⟧ v
      ≡⟨ ⟦⟧∘sels2trm (sels ++ sels0) v ⟩
    v !! (sels ++ sels0)
      ≡⟨ !!∘++ v sels sels0 ⟩
    v !! sels !! sels0
      ≡⟨ sym (⟦⟧∘sels2trm sels0 (v !! sels)) ⟩
    ⟦ sels2trm sels0 ⟧ (v !! sels)
      ≡⟨ refl ⟩
    ⟦⌈ NSelCmp sels0 ⌉⟧ (v !! sels)
  ∎

⟦⌈⌉⟧∘normNCmpSels (IfNilⁿ sels0 nt1 nt2) sels v
  rewrite ⟦⟧∘sels2trm (sels ++ sels0) v
        | ⟦⟧∘sels2trm sels0 (v !! sels)
        | !!∘++ v sels sels0
  = cong₂ (ifNil (v !! sels !! sels0))
          (⟦⌈⌉⟧∘normNCmpSels nt1 sels v)
          (⟦⌈⌉⟧∘normNCmpSels nt2 sels v)

⟦⌈⌉⟧∘normNCmpSels ↯ⁿ sels v = refl

-- normNCmpSels∘++

normNCmpSels∘++ : (nt : NTrm) (sels1 sels2 : List Selector) →
  normNCmpSels nt (sels1 ++ sels2) ≡
  normNCmpSels (normNCmpSels nt sels2) sels1

normNCmpSels∘++ []ⁿ sels1 sels2 = refl
normNCmpSels∘++ (nt1 ∷ⁿ nt2) sels1 sels2
{-
  rewrite normNCmpSels∘++ nt2 sels1 sels2
        | normNCmpSels∘++ nt1 sels1 sels2
  = refl
-}
  =
  begin
    normNCmpSels nt1 (sels1 ++ sels2) ∷ⁿ normNCmpSels nt2 (sels1 ++ sels2)
    ≡⟨ cong (_∷ⁿ_ (normNCmpSels nt1 (sels1 ++ sels2)))
            (normNCmpSels∘++ nt2 sels1 sels2) ⟩
    normNCmpSels nt1 (sels1 ++ sels2) ∷ⁿ
      normNCmpSels (normNCmpSels nt2 sels2) sels1
    ≡⟨ cong (flip _∷ⁿ_ (normNCmpSels (normNCmpSels nt2 sels2) sels1))
            (normNCmpSels∘++ nt1 sels1 sels2) ⟩
    normNCmpSels (normNCmpSels nt1 sels2) sels1 ∷ⁿ
      normNCmpSels (normNCmpSels nt2 sels2) sels1
  ∎

normNCmpSels∘++ (NSelCmp sels) sels1 sels2
  rewrite ++-assoc sels1 sels2 sels
  =  refl

normNCmpSels∘++ (IfNilⁿ sels nt1 nt2) sels1 sels2
  rewrite ++-assoc sels1 sels2 sels
        | normNCmpSels∘++ nt1 sels1 sels2
        | normNCmpSels∘++ nt2 sels1 sels2
  = refl

normNCmpSels∘++  ↯ⁿ sels1 sels2 = refl

-- normNIf

normNIf : (nt0 nt1 nt2 : NTrm) → NTrm

normNIf []ⁿ nt1 nt2 =
  nt1
normNIf (nt' ∷ⁿ nt'') nt1 nt2 =
  nt2
normNIf (NSelCmp sels) nt1 nt2 =
  IfNilⁿ sels nt1 nt2
normNIf (IfNilⁿ sels nt' nt'') nt1 nt2 =
  IfNilⁿ sels (normNIf nt' nt1 nt2) (normNIf nt'' nt1 nt2)
normNIf ↯ⁿ nt1 nt2 =
  ↯ⁿ

-- ⟦⌈⌉⟧∘normNIf

⟦⌈⌉⟧∘normNIf : ∀ (nt1 nt2 nt3 : NTrm) (v : Val) →
  ⟦⌈_⌉⟧ (normNIf nt1 nt2 nt3) v ≡
    ifNil (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt2 v) (⟦⌈_⌉⟧ nt3 v)

⟦⌈⌉⟧∘normNIf []ⁿ nt2 nt3 v = refl
⟦⌈⌉⟧∘normNIf (nt' ∷ⁿ nt'') nt2 nt3 v = refl
⟦⌈⌉⟧∘normNIf (NSelCmp sels) nt2 nt3 v
  with ⟦ sels2trm sels ⟧ v
... | VNil = refl
... | VCons v1 v2 = refl
... | VBottom = refl
⟦⌈⌉⟧∘normNIf (IfNilⁿ sels nt' nt'') nt2 nt3 v
  with ⟦ sels2trm sels ⟧ v
... | VNil        rewrite ⟦⌈⌉⟧∘normNIf nt'  nt2 nt3 v = refl
... | VCons v1 v2 rewrite ⟦⌈⌉⟧∘normNIf nt'' nt2 nt3 v = refl
... | VBottom = refl
⟦⌈⌉⟧∘normNIf ↯ⁿ nt2 nt3 v = refl

-- normNCmp

normNCmp : NTrm → NTrm → NTrm

normNCmp []ⁿ nt2 =
  []ⁿ

normNCmp (nt' ∷ⁿ nt'') nt2 =
  normNCmp nt' nt2 ∷ⁿ normNCmp nt'' nt2

normNCmp (NSelCmp sels) nt2 =
  normSelsNCmp nt2 sels

normNCmp (IfNilⁿ sels nt' nt'') (NSelCmp sels2) =
  IfNilⁿ (sels2 ++ sels) (normNCmpSels nt' sels2) (normNCmpSels nt'' sels2)

normNCmp (IfNilⁿ sels nt' nt'') (IfNilⁿ sels2 nt2' nt2'') =
  IfNilⁿ sels2 (normNCmp (IfNilⁿ sels nt' nt'') nt2')
               (normNCmp (IfNilⁿ sels nt' nt'') nt2'')

normNCmp (IfNilⁿ sels nt' nt'') nt2 =
  normNIf (normSelsNCmp nt2 sels) (normNCmp nt' nt2) (normNCmp nt'' nt2)

normNCmp ↯ⁿ nt2 =
  ↯ⁿ

-- normNCmp∘IfNilⁿ

normNCmp∘IfNilⁿ : (sels1 sels2 : List Selector) →
  (nt1-1 nt1-2 nt2-1 nt2-2 : NTrm) →
  let nt1 = IfNilⁿ sels1 nt1-1 nt1-2 in 
  normNCmp nt1 (IfNilⁿ sels2 nt2-1 nt2-2)
    ≡ IfNilⁿ sels2 (normNCmp nt1 nt2-1) (normNCmp nt1 nt2-2)

normNCmp∘IfNilⁿ sels1 sels2 nt1-1 nt1-2 nt2-1 nt2-2 = refl

--
-- ⟦⌈⌉⟧∘normNCmp
--

⟦⌈⌉⟧∘normNCmp : (nt1 nt2 : NTrm) (v : Val) →
  ⟦⌈_⌉⟧ (normNCmp nt1 nt2) v ≡ ⟦⌈_⌉⟧ nt1 (⟦⌈_⌉⟧ nt2 v)

⟦⌈⌉⟧∘normNCmp []ⁿ nt2 v =
  refl

⟦⌈⌉⟧∘normNCmp (nt' ∷ⁿ nt'') nt2 v
  rewrite ⟦⌈⌉⟧∘normNCmp nt' nt2 v
        | ⟦⌈⌉⟧∘normNCmp nt'' nt2 v
  = refl

⟦⌈⌉⟧∘normNCmp (NSelCmp sels) nt2 v =
  begin
    ⟦⌈_⌉⟧ (normNCmp (NSelCmp sels) nt2) v
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (normSelsNCmp nt2 sels) v
      ≡⟨ ⟦⌈⌉⟧∘normSelsNCmp nt2 sels v ⟩
    (⟦ ⌈ nt2 ⌉ ⟧ v) !! sels
      ≡⟨ sym (⟦⟧∘sels2trm sels (⟦ ⌈ nt2 ⌉ ⟧ v)) ⟩
    ⟦ sels2trm sels ⟧ (⟦ ⌈ nt2 ⌉ ⟧ v)
      ≡⟨ refl ⟩
    ⟦⌈ NSelCmp sels ⌉⟧ (⟦⌈ nt2 ⌉⟧ v)
  ∎

⟦⌈⌉⟧∘normNCmp (IfNilⁿ sels nt' nt'') nt2 v =
  begin
    ⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') nt2) v
      ≡⟨ helper nt2 ⟩
    ifNil (⟦⌈_⌉⟧ (normSelsNCmp nt2 sels) v)
          (⟦⌈_⌉⟧ (normNCmp nt' nt2) v) (⟦⌈_⌉⟧ (normNCmp nt'' nt2) v)
      ≡⟨ ifNil-cong (⟦⌈⌉⟧∘normSelsNCmp nt2 sels v) refl refl ⟩
    ifNil (⟦⌈ nt2 ⌉⟧ v !! sels)
          (⟦⌈_⌉⟧ (normNCmp nt' nt2) v) (⟦⌈_⌉⟧ (normNCmp nt'' nt2) v)
      ≡⟨ ifNil-cong (sym $
           ⟦⟧∘sels2trm sels (⟦ ⌈ nt2 ⌉ ⟧ v))
           (⟦⌈⌉⟧∘normNCmp nt' nt2 v)
           (⟦⌈⌉⟧∘normNCmp nt'' nt2 v) ⟩
    ifNil (⟦ sels2trm sels ⟧ (⟦⌈ nt2 ⌉⟧ v))
          (⟦⌈_⌉⟧ nt' (⟦⌈_⌉⟧ nt2 v)) (⟦⌈_⌉⟧ nt''(⟦⌈_⌉⟧ nt2 v))
      ≡⟨ refl ⟩
    ⟦⌈_⌉⟧ (IfNilⁿ sels nt' nt'') (⟦⌈_⌉⟧ nt2 v)
  ∎
  where
    helper : (nt2 : NTrm) →
      ⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') nt2) v
      ≡
      ifNil (⟦⌈_⌉⟧ (normSelsNCmp nt2 sels) v)
            (⟦⌈_⌉⟧ (normNCmp nt' nt2) v) (⟦⌈_⌉⟧ (normNCmp nt'' nt2) v)

    helper (NSelCmp sels') = begin
      ⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') (NSelCmp sels')) v
        ≡⟨ refl ⟩
      ifNil (⟦ sels2trm (sels' ++ sels) ⟧ v)
            (⟦⌈_⌉⟧ (normNCmpSels nt' sels') v)
            (⟦⌈_⌉⟧ (normNCmpSels nt'' sels') v)
        ≡⟨ ifNil-cong
             (⟦⟧∘sels2trm (sels' ++ sels) v)
             (⟦⌈⌉⟧∘normNCmpSels nt' sels' v)
             (⟦⌈⌉⟧∘normNCmpSels nt'' sels' v) ⟩
      ifNil (v !! (sels' ++ sels))
            (⟦⌈ nt' ⌉⟧ (v !! sels'))
            (⟦⌈ nt'' ⌉⟧ (v !! sels'))
        ≡⟨ ifNil-cong
            (!!∘++ v sels' sels)
            (sym $ cong (⟦ ⌈ nt' ⌉ ⟧) (⟦⟧∘sels2trm sels' v))
            (sym $ cong (⟦ ⌈ nt'' ⌉ ⟧) (⟦⟧∘sels2trm sels' v)) ⟩
      ifNil (v !! sels' !! sels)
            (⟦⌈ nt' ⌉⟧ (⟦⌈ NSelCmp sels' ⌉⟧ v))
            (⟦⌈ nt'' ⌉⟧ (⟦⌈ NSelCmp sels' ⌉⟧ v))
        ≡⟨ ifNil-cong
             (cong (flip _!!_ sels) (sym (⟦⟧∘sels2trm sels' v)))
             (sym $ ⟦⌈⌉⟧∘normNCmp nt' (NSelCmp sels') v)
             (sym $ ⟦⌈⌉⟧∘normNCmp nt'' (NSelCmp sels') v) ⟩
      ifNil (⟦ sels2trm sels' ⟧ v !! sels)
            (⟦⌈_⌉⟧ (normNCmp nt' (NSelCmp sels')) v)
            (⟦⌈_⌉⟧ (normNCmp nt'' (NSelCmp sels')) v)
        ≡⟨ refl ⟩
      ifNil (⟦⌈_⌉⟧ (NSelCmp sels') v !! sels)
            (⟦⌈_⌉⟧ (normNCmp nt' (NSelCmp sels')) v)
            (⟦⌈_⌉⟧ (normNCmp nt'' (NSelCmp sels')) v)
        ≡⟨ ifNil-cong
             (sym (⟦⌈⌉⟧∘normSelsNCmp (NSelCmp sels') sels v))
             refl refl ⟩
      ifNil (⟦⌈_⌉⟧ (normSelsNCmp (NSelCmp sels') sels) v)
            (⟦⌈_⌉⟧ (normNCmp nt' (NSelCmp sels')) v)
            (⟦⌈_⌉⟧ (normNCmp nt'' (NSelCmp sels')) v)
      ∎

    helper (IfNilⁿ sels' nt1 nt3) = begin
      ⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') (IfNilⁿ sels' nt1 nt3)) v
        ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
                (normNCmp∘IfNilⁿ sels sels' nt' nt'' nt1 nt3) ⟩
      ⟦⌈_⌉⟧ (IfNilⁿ sels'
        (normNCmp (IfNilⁿ sels nt' nt'') nt1)
        (normNCmp (IfNilⁿ sels nt' nt'') nt3)) v
        ≡⟨ refl ⟩
      ifNil (⟦ sels2trm sels' ⟧ v)
        (⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') nt1) v)
        (⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') nt3) v)
        ≡⟨ ifNil-cong
             (⟦⟧∘sels2trm sels' v)
             (⟦⌈⌉⟧∘normNCmp (IfNilⁿ sels nt' nt'') nt1 v)
             (⟦⌈⌉⟧∘normNCmp (IfNilⁿ sels nt' nt'') nt3 v) ⟩
      ifNil (v !! sels')
        (⟦⌈_⌉⟧ (IfNilⁿ sels nt' nt'') (⟦⌈_⌉⟧ nt1 v))
        (⟦⌈_⌉⟧ (IfNilⁿ sels nt' nt'') (⟦⌈_⌉⟧ nt3 v))
        ≡⟨ refl ⟩
      ifNil (v !! sels')
        (ifNil (⟦ sels2trm sels ⟧ (⟦⌈_⌉⟧ nt1 v))
               (⟦⌈_⌉⟧ nt' (⟦⌈_⌉⟧ nt1 v))
               (⟦⌈_⌉⟧ nt'' (⟦⌈_⌉⟧ nt1 v)))
        (ifNil (⟦ sels2trm sels ⟧ (⟦⌈_⌉⟧ nt3 v))
               (⟦⌈_⌉⟧ nt' (⟦⌈_⌉⟧ nt3 v))
               (⟦⌈_⌉⟧ nt'' (⟦⌈_⌉⟧ nt3 v)))
        ≡⟨ cong₂ (ifNil (v !! sels'))
                 (ifNil-cong (⟦⟧∘sels2trm sels (⟦⌈_⌉⟧ nt1 v)) refl refl)
                 (ifNil-cong (⟦⟧∘sels2trm sels (⟦⌈_⌉⟧ nt3 v)) refl refl) ⟩
      ifNil (v !! sels')
        (ifNil (⟦⌈_⌉⟧ nt1 v !! sels)
               (⟦⌈_⌉⟧ nt' (⟦⌈_⌉⟧ nt1 v))
               (⟦⌈_⌉⟧ nt'' (⟦⌈_⌉⟧ nt1 v)))
        (ifNil (⟦⌈_⌉⟧ nt3 v !! sels)
               (⟦⌈_⌉⟧ nt' (⟦⌈_⌉⟧ nt3 v))
               (⟦⌈_⌉⟧ nt'' (⟦⌈_⌉⟧ nt3 v)))
        ≡⟨ helper₂ (v !! sels')
                   (⟦⌈_⌉⟧ nt1 v !! sels)
                   (⟦⌈_⌉⟧ nt3 v !! sels)
                   (⟦⌈_⌉⟧ nt') (⟦⌈_⌉⟧ nt'')
                   (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)
         ⟩
      ifNil (v !! sels')
            (ifNil (⟦⌈_⌉⟧ nt1 v !! sels)
                   (⟦⌈_⌉⟧ nt' (ifNil (v !! sels')
                                     (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
                   (⟦⌈_⌉⟧ nt'' (ifNil (v !! sels')
                                       (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v))))
            (ifNil (⟦⌈_⌉⟧ nt3 v !! sels)
                   (⟦⌈_⌉⟧ nt' (ifNil (v !! sels')
                                      (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
                   (⟦⌈_⌉⟧ nt'' (ifNil (v !! sels')
                                       (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v))))
        ≡⟨ sym $ ifNil∘ifNil (v !! sels') ⟩
      ifNil (ifNil (v !! sels')
                   (⟦⌈_⌉⟧ nt1 v !! sels)
                   (⟦⌈_⌉⟧ nt3 v !! sels))
            (⟦⌈_⌉⟧ nt' (ifNil (v !! sels')
                              (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
            (⟦⌈_⌉⟧ nt'' (ifNil (v !! sels')
                                (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
        ≡⟨ ifNil-cong (sym $ !!∘ifNil (v !! sels') sels) refl refl ⟩
      ifNil (ifNil (v !! sels') (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v) !! sels)
            (⟦⌈_⌉⟧ nt' (ifNil (v !! sels') (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
            (⟦⌈_⌉⟧ nt'' (ifNil (v !! sels') (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
        ≡⟨ ifNil-cong
             (cong (flip _!!_ sels)
                   (ifNil-cong (sym $ ⟦⟧∘sels2trm sels' v) refl refl))
             (cong (⟦⌈_⌉⟧ nt')
                   (ifNil-cong (sym $ ⟦⟧∘sels2trm sels' v) refl refl))
             (cong (⟦⌈_⌉⟧ nt'')
                   (ifNil-cong (sym $ ⟦⟧∘sels2trm sels' v) refl refl)) ⟩
      ifNil (ifNil (⟦ sels2trm sels' ⟧ v)
                   (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v) !! sels)
            (⟦⌈_⌉⟧ nt' (ifNil (⟦ sels2trm sels' ⟧ v)
                              (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
            (⟦⌈_⌉⟧ nt'' (ifNil (⟦ sels2trm sels' ⟧ v)
                               (⟦⌈_⌉⟧ nt1 v) (⟦⌈_⌉⟧ nt3 v)))
        ≡⟨ refl ⟩
      ifNil (⟦⌈_⌉⟧ (IfNilⁿ sels' nt1 nt3) v !! sels)
            (⟦⌈_⌉⟧ nt' (⟦⌈_⌉⟧ (IfNilⁿ sels' nt1 nt3) v))
            (⟦⌈_⌉⟧ nt'' (⟦⌈_⌉⟧ (IfNilⁿ sels' nt1 nt3) v))
        ≡⟨ ifNil-cong
             (sym $ ⟦⌈⌉⟧∘normSelsNCmp (IfNilⁿ sels' nt1 nt3) sels v)
             (sym $ ⟦⌈⌉⟧∘normNCmp nt' (IfNilⁿ sels' nt1 nt3) v)
             (sym $ ⟦⌈⌉⟧∘normNCmp nt'' (IfNilⁿ sels' nt1 nt3) v) ⟩
      ifNil (⟦⌈_⌉⟧ (normSelsNCmp (IfNilⁿ sels' nt1 nt3) sels) v)
            (⟦⌈_⌉⟧ (normNCmp nt' (IfNilⁿ sels' nt1 nt3)) v)
            (⟦⌈_⌉⟧ (normNCmp nt'' (IfNilⁿ sels' nt1 nt3)) v)
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

    helper []ⁿ = begin
      ⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') []ⁿ) v
        ≡⟨ refl ⟩
      ⟦⌈_⌉⟧ (normNIf (normSelsNCmp []ⁿ sels)
                      (normNCmp nt' []ⁿ) (normNCmp nt'' []ⁿ)) v
        ≡⟨ ⟦⌈⌉⟧∘normNIf
             (normSelsNCmp []ⁿ sels)
             (normNCmp nt' []ⁿ) (normNCmp nt'' []ⁿ) v ⟩
      ifNil (⟦⌈_⌉⟧ (normSelsNCmp []ⁿ sels) v)
            (⟦⌈_⌉⟧ (normNCmp nt' []ⁿ) v) (⟦⌈_⌉⟧ (normNCmp nt'' []ⁿ) v)
      ∎

    helper (nt1 ∷ⁿ nt3) = begin
      ⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') (nt1 ∷ⁿ nt3)) v
        ≡⟨ refl ⟩
      ⟦⌈_⌉⟧ (normNIf (normSelsNCmp (nt1 ∷ⁿ nt3) sels)
                      (normNCmp nt' (nt1 ∷ⁿ nt3))
                      (normNCmp nt'' (nt1 ∷ⁿ nt3))) v
        ≡⟨ ⟦⌈⌉⟧∘normNIf
             (normSelsNCmp (nt1 ∷ⁿ nt3) sels)
             (normNCmp nt' (nt1 ∷ⁿ nt3)) (normNCmp nt'' (nt1 ∷ⁿ nt3)) v ⟩
      ifNil (⟦⌈_⌉⟧ (normSelsNCmp (nt1 ∷ⁿ nt3) sels) v)
            (⟦⌈_⌉⟧ (normNCmp nt' (nt1 ∷ⁿ nt3)) v)
            (⟦⌈_⌉⟧ (normNCmp nt'' (nt1 ∷ⁿ nt3)) v)
      ∎

    helper ↯ⁿ = begin
      ⟦⌈_⌉⟧ (normNCmp (IfNilⁿ sels nt' nt'') ↯ⁿ) v
        ≡⟨ refl ⟩
      ⟦⌈_⌉⟧ (normNIf (normSelsNCmp ↯ⁿ sels)
                      (normNCmp nt' ↯ⁿ) (normNCmp nt'' ↯ⁿ)) v
        ≡⟨ ⟦⌈⌉⟧∘normNIf (normSelsNCmp ↯ⁿ sels)
                          (normNCmp nt' ↯ⁿ) (normNCmp nt'' ↯ⁿ) v ⟩
      ifNil (⟦⌈_⌉⟧ (normSelsNCmp ↯ⁿ sels) v)
            (⟦⌈_⌉⟧ (normNCmp nt' ↯ⁿ) v)
            (⟦⌈_⌉⟧ (normNCmp nt'' ↯ⁿ) v)
      ∎

⟦⌈⌉⟧∘normNCmp ↯ⁿ nt2 v =
  refl

-- normConv

normConv : (t : Trm) → NTrm

normConv [] = []ⁿ
normConv (t1 ∷ t2) = normConv t1  ∷ⁿ normConv t2
normConv (Sel sel) = NSelCmp [ sel ]
normConv Id = NSelCmp []
normConv (t1 $$ t2) = normNCmp (normConv t1) (normConv t2)
normConv (IfNil t0 t1 t2) = normNIf (normConv t0) (normConv t1) (normConv t2)
normConv Bottom = ↯ⁿ

--
-- The main theorem establishing the correctness of normalization.
--

-- ⟦⌈⌉⟧∘normConv

⟦⌈⌉⟧∘normConv : (t : Trm) (v : Val) →
  ⟦⌈ normConv t ⌉⟧ v ≡ ⟦ t ⟧ v

⟦⌈⌉⟧∘normConv [] v =
  refl
⟦⌈⌉⟧∘normConv (t1 ∷ t2) v
  rewrite ⟦⌈⌉⟧∘normConv t1 v | ⟦⌈⌉⟧∘normConv t2 v
  = refl
⟦⌈⌉⟧∘normConv (Sel sel) v =
  refl
⟦⌈⌉⟧∘normConv Id v =
  refl
⟦⌈⌉⟧∘normConv (t1 $$ t2) v = begin
  ⟦⌈_⌉⟧ (normConv (t1 $$ t2)) v
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (normNCmp (normConv t1) (normConv t2)) v
    ≡⟨ ⟦⌈⌉⟧∘normNCmp (normConv t1) (normConv t2) v ⟩
  ⟦⌈_⌉⟧ (normConv t1) (⟦⌈_⌉⟧ (normConv t2) v)
    ≡⟨ cong (⟦⌈_⌉⟧ (normConv t1)) (⟦⌈⌉⟧∘normConv t2 v) ⟩
  ⟦⌈_⌉⟧ (normConv t1) (⟦ t2 ⟧ v)
    ≡⟨ ⟦⌈⌉⟧∘normConv t1 (⟦ t2 ⟧ v) ⟩
  ⟦ t1 ⟧ (⟦ t2 ⟧ v)
    ≡⟨ refl ⟩
  ⟦ t1 $$ t2 ⟧ v
  ∎
⟦⌈⌉⟧∘normConv (IfNil t0 t1 t2) v = begin
  ⟦⌈_⌉⟧ (normConv (IfNil t0 t1 t2)) v
    ≡⟨ refl ⟩
  ⟦⌈_⌉⟧ (normNIf (normConv t0) (normConv t1) (normConv t2)) v
    ≡⟨ ⟦⌈⌉⟧∘normNIf (normConv t0) (normConv t1) (normConv t2) v ⟩
  ifNil (⟦⌈_⌉⟧ (normConv t0) v)
        (⟦⌈_⌉⟧ (normConv t1) v) (⟦⌈_⌉⟧ (normConv t2) v)
    ≡⟨ ifNil-cong (⟦⌈⌉⟧∘normConv t0 v)
                  (⟦⌈⌉⟧∘normConv t1 v) (⟦⌈⌉⟧∘normConv t2 v) ⟩
  ifNil (⟦ t0 ⟧ v) (⟦ t1 ⟧ v) (⟦ t2 ⟧ v)
    ≡⟨ refl ⟩
  ⟦ IfNil t0 t1 t2 ⟧ v
  ∎
⟦⌈⌉⟧∘normConv ↯ v =
  refl

--
-- Emulating substitutions
--

-- replaceAt

replaceAt : (sels : List Selector) (t t′ : NTrm) → NTrm

replaceAt [] t t′ = t′
replaceAt (HD ∷ sels) t t′ =
  replaceAt sels (normSelNCmp t HD) t′ ∷ⁿ normSelNCmp t TL
replaceAt (TL ∷ sels) t t′ =
  normSelNCmp t HD ∷ⁿ replaceAt sels (normSelNCmp t TL) t′

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
  replaceAt (sels1 ++ sels2) (normSelNCmp nt HD) nt′ ∷ⁿ normSelNCmp nt TL
    ≡⟨ cong (flip _∷ⁿ_ (normSelNCmp nt TL))
            (replaceAt∘++ sels1 sels2 (normSelNCmp nt HD) nt′) ⟩
  replaceAt sels1 (normSelNCmp nt HD)
            (replaceAt sels2 (normSelsNCmp (normSelNCmp nt HD) sels1) nt′) ∷ⁿ
        normSelNCmp nt TL
    ≡⟨ refl ⟩
  replaceAt (HD ∷ sels1) nt
            (replaceAt sels2 (normSelsNCmp nt (HD ∷ sels1)) nt′)
  ∎
replaceAt∘++ (TL ∷ sels1) sels2 nt nt′ =
  cong (_∷ⁿ_ (normSelNCmp nt HD))
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
