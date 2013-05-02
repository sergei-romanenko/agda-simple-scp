module ExpLang where

open import Data.List
open import Data.List.Reverse
open import Data.List.Properties
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
 
----------
-- Values
----------

-- Values are like Lisp S-expressions.
-- []ˣ is a (single) atom.
-- ↯ˣ denotes an "error" value.

infixr 5 _∷ˣ_

data Val : Set where
  []ˣ  : Val
  _∷ˣ_ : (v1 v2 : Val) → Val
  ↯ˣ   : Val 

-- v₁ ≢ v₂

∷ˣ≢[]ˣ : ∀ {v1 v2} → v1 ∷ˣ v2 ≢ []ˣ
∷ˣ≢[]ˣ = λ ()

∷ˣ≢↯ˣ : ∀ {v1 v2} → v1 ∷ˣ v2 ≢ ↯ˣ
∷ˣ≢↯ˣ = λ ()

↯ˣ≢[]ˣ : ↯ˣ ≢ []ˣ
↯ˣ≢[]ˣ = λ ()

-------------
-- Selectors
-------------

data Selector : Set where
  HD : Selector
  TL : Selector

infixl 4 _!_ _!!_

-- _!_

_!_ : (v : Val) → (sel : Selector) → Val

[]ˣ ! sel = ↯ˣ
v1 ∷ˣ v2 ! HD = v1
v1 ∷ˣ v2 ! TL = v2
↯ˣ ! sel = ↯ˣ

-- _!!_

_!!_ : (v : Val) (sels : List Selector) → Val

v !! [] = v
v !! (x ∷ xs) = (v ! x) !! xs

-- !!-is-foldl

!!-is-foldl : ∀ v sels →
  v !! sels ≡ foldl _!_ v sels
!!-is-foldl v [] = refl
!!-is-foldl v (x ∷ xs) = !!-is-foldl (v ! x) xs

-- _!!_ is strict.

-- ↯ˣ-!!

↯ˣ-!! : ∀ (sels : List Selector) →
  ↯ˣ !! sels ≡ ↯ˣ

↯ˣ-!! [] = refl
↯ˣ-!! (sel ∷ sels) = ↯ˣ-!! sels

-- !!∘++

!!∘++ : ∀ (v : Val) (sels1 sels2 : List Selector) →
  v !! (sels1 ++ sels2) ≡ v !! sels1 !! sels2

!!∘++ v [] sels2 = refl
!!∘++ v (sel ∷ xs) sels2 =
  !!∘++ (v ! sel) xs sels2

-- Updating a subtree in a value

-- _[_]≔_

infixl 6 _[_]≔_

_[_]≔_ : Val → (sels : List Selector) → Val → Val

v [ [] ]≔ v′ = v′
v [ HD ∷ sels ]≔ v′ = (v ! HD) [ sels ]≔ v′ ∷ˣ (v ! TL)
v [ TL ∷ sels ]≔ v′ = (v ! HD) ∷ˣ (v ! TL) [ sels ]≔ v′

-- _[_]≔_ is correct with respect to _!!_

[]≔∘!! : ∀ sels v v′ →
  (v [ sels ]≔ v′) !! sels ≡ v′

[]≔∘!! [] v v′ = refl
[]≔∘!! (HD ∷ sels) v v′ = []≔∘!! sels (v ! HD) v′
[]≔∘!! (TL ∷ sels) v v′ = []≔∘!! sels (v ! TL) v′

---------------------------
-- Conditional expressions
---------------------------

-- ifNil

ifNil : (v0 v1 v2 : Val) → Val

ifNil []ˣ v1 v2 = v1
ifNil (_ ∷ˣ _) v1 v2 = v2
ifNil ↯ˣ v1 v2 = ↯ˣ

-- ifNil-cong

ifNil-cong : ∀ {v0 v0′ v1 v1′ v2 v2′ : Val} →
  v0 ≡ v0′ → v1 ≡ v1′ → v2 ≡ v2′ →
  ifNil v0 v1 v2 ≡ ifNil v0′ v1′ v2′

ifNil-cong refl refl refl = refl

-- ifNil-distr

ifNil-distr : ∀ (f : Val → Val) → f ↯ˣ ≡ ↯ˣ → ∀ v0 {v1 v2} →
  f (ifNil v0 v1 v2) ≡ ifNil v0 (f v1) (f v2)

ifNil-distr f fb []ˣ = refl
ifNil-distr f fb (v1 ∷ˣ v2) = refl
ifNil-distr f fb ↯ˣ = fb

-- ifNil∘ifNil

ifNil∘ifNil : ∀ u0 {u1 u2 v1 v2} →
  ifNil (ifNil u0 u1 u2) v1 v2 ≡ ifNil u0 (ifNil u1 v1 v2) (ifNil u2 v1 v2)

ifNil∘ifNil []ˣ = refl
ifNil∘ifNil (_ ∷ˣ _) = refl
ifNil∘ifNil ↯ˣ = refl

-- !!∘ifNil

!!∘ifNil : ∀ v0 {v1 v2} (sels : List Selector) →
  (ifNil v0 v1 v2) !! sels ≡
    ifNil v0 (v1 !! sels) (v2 !! sels)

!!∘ifNil v0 {v1} {v2} sels =
  ifNil-distr (flip _!!_ sels) (↯ˣ-!! sels) v0

-- !∘ifNil

!∘ifNil : ∀ v0 {v1 v2} (sel : Selector) →
  (ifNil v0 v1 v2) ! sel ≡
    ifNil v0 (v1 ! sel) (v2 ! sel)

!∘ifNil v0 {v1} {v2} sel = !!∘ifNil v0 (sel ∷ [])

----------------------
-- Simple expressions
----------------------

-- The language of expressions is "variable free".
-- All expressions denote functions of type Val → Val.

infixr 5 _∷_
infixr 6 _$$_

data Trm : Set where
  []    : Trm
  _∷_   : (t1 t2 : Trm) → Trm 
  Hd    : Trm
  Tl    : Trm
  Id    : Trm
  _$$_  : (t1 t2 : Trm) → Trm
  IfNil : (t0 t1 t2 : Trm) → Trm
  ↯     : Trm

-- As the language of expressions is not Turing-complete,
-- its semantics is given as a total function.

-- ⟦_⟧

⟦_⟧ : (t : Trm) (v : Val) →  Val

⟦ [] ⟧ v = []ˣ
⟦ t1 ∷ t2 ⟧ v = ⟦ t1 ⟧ v ∷ˣ ⟦ t2 ⟧ v
⟦ Hd ⟧ v = v ! HD
⟦ Tl ⟧ v = v ! TL
⟦ Id ⟧ v = v
⟦ t1 $$ t2 ⟧ v = ⟦ t1 ⟧ (⟦ t2 ⟧ v)
⟦ IfNil t0 t1 t2 ⟧ v =
  ifNil (⟦ t0 ⟧ v) (⟦ t1 ⟧ v) (⟦ t2 ⟧ v) 
⟦ ↯ ⟧ v = ↯ˣ


-- "Applying" selectors to expressions
-- (symbolic evaluation with some simplifications).

-- _⁉_

_⁉_ : (t : Trm) → (sel : Selector) → Trm

Id ⁉ HD = Hd
Id ⁉ TL = Tl
t  ⁉ HD = Hd $$ t
t  ⁉ TL = Tl $$ t

-- _⁉_ is correct with respect to _!_

-- ⟦⟧∘⁉

⟦⟧∘⁉ : ∀ t sel v → ⟦ t ⁉ sel ⟧ v ≡ ⟦ t ⟧ v ! sel

⟦⟧∘⁉ [] HD v = refl
⟦⟧∘⁉ [] TL v = refl
⟦⟧∘⁉ (t1 ∷ t2) HD v = refl
⟦⟧∘⁉ (t1 ∷ t2) TL v = refl
⟦⟧∘⁉ Hd HD v = refl
⟦⟧∘⁉ Hd TL v = refl
⟦⟧∘⁉ Tl HD v = refl
⟦⟧∘⁉ Tl TL v = refl
⟦⟧∘⁉ Id HD v = refl
⟦⟧∘⁉ Id TL v = refl
⟦⟧∘⁉ (t1 $$ t2) HD v = refl
⟦⟧∘⁉ (t1 $$ t2) TL v = refl
⟦⟧∘⁉ (IfNil t0 t1 t2) HD v = refl
⟦⟧∘⁉ (IfNil t0 t1 t2) TL v = refl
⟦⟧∘⁉ ↯ HD v = refl
⟦⟧∘⁉ ↯ TL v = refl

-- ⟦⟧∘foldr⁉

⟦⟧∘foldr⁉ : ∀ rsels v →
  ⟦ foldr (flip _⁉_) Id rsels ⟧ v ≡
  foldr (flip _!_) v rsels

⟦⟧∘foldr⁉ [] v = refl

⟦⟧∘foldr⁉ (sel ∷ rsels) v =
  begin
    ⟦ foldr (flip _⁉_) Id (sel ∷ rsels) ⟧ v
      ≡⟨ refl ⟩
    ⟦ foldr (flip _⁉_) Id rsels ⁉ sel ⟧ v
      ≡⟨ ⟦⟧∘⁉ (foldr (flip _⁉_) Id rsels) sel v ⟩
    ⟦ foldr (flip _⁉_) Id rsels ⟧ v ! sel
      ≡⟨ cong (flip _!_ sel) (⟦⟧∘foldr⁉ rsels v) ⟩
    (foldr (flip _!_) v rsels) ! sel
      ≡⟨ refl ⟩
    foldr (flip _!_) v (sel ∷ rsels)
  ∎

-- Sequences of selectors applied symbolically

-- ⟪_⟫

⟪_⟫ : (sels : List Selector) → Trm
⟪_⟫ sels = foldl _⁉_ Id sels

-- ⟦⟧∘⟪⟫

⟦⟧∘⟪⟫ : ∀ sels v →
  ⟦ ⟪ sels ⟫ ⟧ v ≡ v !! sels

⟦⟧∘⟪⟫ sels v =
  begin
    ⟦ ⟪ sels ⟫ ⟧ v
      ≡⟨ refl ⟩
    ⟦ foldl _⁉_ Id sels ⟧ v
      ≡⟨ cong (flip ⟦_⟧ v) (sym $ foldr∘reverse (flip _⁉_) Id sels) ⟩
    ⟦ foldr (flip _⁉_) Id (reverse sels) ⟧ v
      ≡⟨ ⟦⟧∘foldr⁉ (foldl (flip _∷_) [] sels) v ⟩
    foldr (flip _!_) v (reverse sels)
      ≡⟨ foldr∘reverse (flip _!_) v sels ⟩
    foldl _!_ v sels
      ≡⟨ sym $ !!-is-foldl v sels ⟩
    v !! sels
  ∎

---------------------------------------
-- Normalization of simple expressions
---------------------------------------

-- Expressions in "normal form" are represented by a special data type.
-- In normal forms
--   * Function composition can only be applied to a pair of selectors.
--   * Tests in conditional expressions are selector compositions
--     (in reverse order, so that they can be directly interpreted as
--     positions in the binary trees of values).

-- NTrm

infixr 5 _∷ⁿ_

data NTrm : Set where
  []ⁿ    : NTrm 
  _∷ⁿ_   : (nt1 nt2 : NTrm) → NTrm 
  ⟪_⟫ⁿ   : (sels : List Selector) → NTrm
  IfNilⁿ : (sels : List Selector) → (nt1 nt2 : NTrm) → NTrm
  ↯ⁿ     : NTrm

-- NTrm is a "subset" of Trm, as there is an injection NTrm → Trm.

-- ⌈_⌉ 

⌈_⌉ : (nt : NTrm) → Trm

⌈ []ⁿ ⌉ = []
⌈ nt1 ∷ⁿ nt2 ⌉ = ⌈ nt1 ⌉ ∷ ⌈ nt2 ⌉
⌈ ⟪ sels ⟫ⁿ ⌉ = ⟪ sels ⟫
⌈  IfNilⁿ sels nt1 nt2 ⌉ =
  IfNil ⟪ sels ⟫ ⌈ nt1 ⌉ ⌈ nt2 ⌉
⌈ ↯ⁿ ⌉ = ↯

-- The composition of ⟦_⟧ and ⌈_⌉ is defined "just for beauty"
-- (to spare 2 spaces in formulas).

-- ⟦⌈_⌉⟧

⟦⌈_⌉⟧ : (nt : NTrm) (v : Val) → Val
⟦⌈ nt ⌉⟧ v = ⟦ ⌈ nt ⌉ ⟧ v


--
-- Symbolic application of a selector to a normal-form term.
--

infixl 4 _!ⁿ_ _!!ⁿ_

-- _!ⁿ_

_!ⁿ_ : (nt : NTrm) (sel : Selector) → NTrm

[]ⁿ !ⁿ sel = ↯ⁿ
nt1 ∷ⁿ nt2 !ⁿ HD = nt1
nt1 ∷ⁿ nt2 !ⁿ TL = nt2
⟪ sels ⟫ⁿ !ⁿ sel = ⟪ sels ++ [ sel ] ⟫ⁿ
IfNilⁿ sels nt1 nt2 !ⁿ sel =
  IfNilⁿ sels (nt1 !ⁿ sel) (nt2 !ⁿ sel)
↯ⁿ !ⁿ sel = ↯ⁿ

-- _!ⁿ_ is correct with respect to _!_

-- ⟦⌈⌉⟧∘!ⁿ

⟦⌈⌉⟧∘!ⁿ : (nt : NTrm) (sel : Selector) (v : Val) →
  ⟦⌈ nt !ⁿ sel ⌉⟧  v ≡ ⟦⌈ nt ⌉⟧ v ! sel

⟦⌈⌉⟧∘!ⁿ []ⁿ sel v = refl
⟦⌈⌉⟧∘!ⁿ (nt1 ∷ⁿ nt2) HD v = refl
⟦⌈⌉⟧∘!ⁿ (nt1 ∷ⁿ nt2) TL v = refl

⟦⌈⌉⟧∘!ⁿ ⟪ sels ⟫ⁿ sel v =
  begin
    ⟦⌈ ⟪ sels ⟫ⁿ !ⁿ sel ⌉⟧ v
      ≡⟨ refl ⟩
    ⟦⌈ ⟪ sels ++ [ sel ] ⟫ⁿ ⌉⟧ v
      ≡⟨ refl ⟩
    ⟦ ⌈ ⟪ sels ++ [ sel ] ⟫ⁿ ⌉ ⟧ v
      ≡⟨ refl ⟩
    ⟦ ⟪ sels ++ [ sel ] ⟫ ⟧ v
      ≡⟨ ⟦⟧∘⟪⟫ (sels ++ [ sel ]) v ⟩
    v !! (sels ++ [ sel ])
      ≡⟨ !!∘++ v sels [ sel ] ⟩
    v !! sels !! [ sel ]
      ≡⟨ refl ⟩
    v !! sels ! sel
      ≡⟨ sym $ cong (flip _!_ sel) (⟦⟧∘⟪⟫ sels v) ⟩
    ⟦ ⟪ sels ⟫ ⟧ v ! sel
      ≡⟨ refl ⟩
    ⟦ ⌈ ⟪ sels ⟫ⁿ ⌉ ⟧ v ! sel
      ≡⟨ refl ⟩
    ⟦⌈ ⟪ sels ⟫ⁿ ⌉⟧ v ! sel
  ∎

⟦⌈⌉⟧∘!ⁿ (IfNilⁿ sels nt1 nt2) sel v =
  begin
    ⟦⌈ IfNilⁿ sels nt1 nt2 !ⁿ sel ⌉⟧ v
      ≡⟨ refl ⟩
    ifNil (⟦ ⟪ sels ⟫ ⟧ v)
          (⟦⌈ nt1 !ⁿ sel ⌉⟧ v)
          (⟦⌈ nt2 !ⁿ sel ⌉⟧ v)
      ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
               (⟦⌈⌉⟧∘!ⁿ nt1 sel v)
               (⟦⌈⌉⟧∘!ⁿ nt2 sel v) ⟩
    ifNil (⟦ ⟪ sels ⟫ ⟧  v)
          (⟦⌈ nt1 ⌉⟧ v ! sel)
          (⟦⌈ nt2 ⌉⟧ v ! sel)
      ≡⟨ sym $ !∘ifNil (⟦ ⟪ sels ⟫ ⟧  v) sel ⟩
    ifNil (⟦ ⟪ sels ⟫ ⟧ v) (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt2 ⌉⟧ v) ! sel
      ≡⟨ refl ⟩
    ⟦⌈ IfNilⁿ sels nt1 nt2 ⌉⟧ v ! sel
  ∎

⟦⌈⌉⟧∘!ⁿ ↯ⁿ sel v = refl


--
-- Symbolic application of a selector list to a normal term.
--

-- _!!ⁿ_

_!!ⁿ_ : (nt : NTrm) (sels : List Selector) → NTrm

nt !!ⁿ sels =
  foldl _!ⁿ_ nt sels

-- _!!ⁿ_ is strict.

-- ↯ⁿ-!!ⁿ

↯ⁿ-!!ⁿ : ∀ sels → ↯ⁿ !!ⁿ sels ≡ ↯ⁿ

↯ⁿ-!!ⁿ [] = refl
↯ⁿ-!!ⁿ (x ∷ xs) = ↯ⁿ-!!ⁿ xs

-- _!!ⁿ_ is correct with respect to _!!_

-- ⟦⌈⌉⟧∘!!ⁿ

⟦⌈⌉⟧∘!!ⁿ :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    ⟦⌈ nt !!ⁿ sels ⌉⟧ v ≡
    ⟦⌈ nt ⌉⟧ v !! sels

⟦⌈⌉⟧∘!!ⁿ nt [] v = refl

⟦⌈⌉⟧∘!!ⁿ nt (sel ∷ sels) v =
  begin
    ⟦⌈ nt !!ⁿ sel ∷ sels ⌉⟧ v
      ≡⟨ refl ⟩
    ⟦⌈ nt !ⁿ sel !!ⁿ sels ⌉⟧ v
      ≡⟨ ⟦⌈⌉⟧∘!!ⁿ (nt !ⁿ sel) sels v ⟩
    ⟦⌈ nt !ⁿ sel ⌉⟧ v !! sels
      ≡⟨ cong (flip _!!_ sels)
              (⟦⌈⌉⟧∘!ⁿ nt sel v) ⟩
    ⟦⌈ nt ⌉⟧ v ! sel !! sels
      ≡⟨ refl ⟩
    ⟦⌈ nt ⌉⟧ v !! (sel ∷ sels)
  ∎

-- !!ⁿ∘⟪⟫ⁿ

!!ⁿ∘⟪⟫ⁿ : ∀ (sels1 sels2 : List Selector) →
  ⟪ sels1 ⟫ⁿ !!ⁿ sels2 ≡ ⟪ sels1 ++ sels2 ⟫ⁿ

!!ⁿ∘⟪⟫ⁿ sels1 []
  rewrite proj₂ LM.identity sels1
  = refl
!!ⁿ∘⟪⟫ⁿ sels1 (sel ∷ sels) = begin
  ⟪ sels1 ⟫ⁿ !!ⁿ sel ∷ sels
    ≡⟨ refl ⟩
  ⟪ sels1 ++ sel ∷ [] ⟫ⁿ !!ⁿ sels
    ≡⟨ !!ⁿ∘⟪⟫ⁿ (sels1 ++ sel ∷ []) sels ⟩
  ⟪ (sels1 ++ sel ∷ []) ++ sels ⟫ⁿ
    ≡⟨ cong ⟪_⟫ⁿ (LM.assoc sels1 (sel ∷ []) sels) ⟩
  ⟪ sels1 ++ (sel ∷ [] ++ sels) ⟫ⁿ
    ≡⟨ refl ⟩
  ⟪ sels1 ++ sel ∷ sels ⟫ⁿ
  ∎

--
-- Symbolic composition of a normal term with a selector list.
--

-- _○⟪_⟫ⁿ

infixl 4 _○⟪_⟫ⁿ _○_

_○⟪_⟫ⁿ : (nt : NTrm) (sels : List Selector) → NTrm

[]ⁿ ○⟪ sels ⟫ⁿ =
  []ⁿ
nt1 ∷ⁿ nt2 ○⟪ sels ⟫ⁿ =
  (nt1 ○⟪ sels ⟫ⁿ) ∷ⁿ (nt2 ○⟪ sels ⟫ⁿ)
⟪ sels2 ⟫ⁿ ○⟪ sels ⟫ⁿ =
  ⟪ sels ++ sels2 ⟫ⁿ
IfNilⁿ sels2 nt1 nt2 ○⟪ sels ⟫ⁿ =
  IfNilⁿ (sels ++ sels2) (nt1 ○⟪ sels ⟫ⁿ) (nt2 ○⟪ sels ⟫ⁿ)
↯ⁿ ○⟪ sels ⟫ⁿ =
  ↯ⁿ

-- _○⟪_⟫ⁿ is correct with respect to _!!_

-- ⟦⌈⌉⟧∘○⟪⟫ⁿ

⟦⌈⌉⟧∘○⟪⟫ⁿ :
  (nt : NTrm) (sels : List Selector) (v : Val) →
    ⟦⌈ nt ○⟪ sels ⟫ⁿ ⌉⟧ v ≡ ⟦⌈ nt ⌉⟧ (v !! sels)

⟦⌈⌉⟧∘○⟪⟫ⁿ []ⁿ sels v = refl

⟦⌈⌉⟧∘○⟪⟫ⁿ (nt1 ∷ⁿ nt2) sels v
  rewrite ⟦⌈⌉⟧∘○⟪⟫ⁿ nt1 sels v
        | ⟦⌈⌉⟧∘○⟪⟫ⁿ nt2 sels v = refl

⟦⌈⌉⟧∘○⟪⟫ⁿ ⟪ sels0 ⟫ⁿ sels v =
  begin
    ⟦⌈ ⟪ sels0 ⟫ⁿ ○⟪ sels ⟫ⁿ ⌉⟧ v
      ≡⟨ refl ⟩
    ⟦ ⟪ sels ++ sels0 ⟫ ⟧ v
      ≡⟨ ⟦⟧∘⟪⟫ (sels ++ sels0) v ⟩
    v !! (sels ++ sels0)
      ≡⟨ !!∘++ v sels sels0 ⟩
    v !! sels !! sels0
      ≡⟨ sym $ ⟦⟧∘⟪⟫ sels0 (v !! sels) ⟩
    ⟦ ⟪ sels0 ⟫ ⟧ (v !! sels)
      ≡⟨ refl ⟩
    ⟦⌈ ⟪ sels0 ⟫ⁿ ⌉⟧ (v !! sels)
  ∎

⟦⌈⌉⟧∘○⟪⟫ⁿ (IfNilⁿ sels0 nt1 nt2) sels v
  rewrite ⟦⟧∘⟪⟫ (sels ++ sels0) v
        | ⟦⟧∘⟪⟫ sels0 (v !! sels)
        | !!∘++ v sels sels0
  = cong₂ (ifNil (v !! sels !! sels0))
          (⟦⌈⌉⟧∘○⟪⟫ⁿ nt1 sels v)
          (⟦⌈⌉⟧∘○⟪⟫ⁿ nt2 sels v)

⟦⌈⌉⟧∘○⟪⟫ⁿ ↯ⁿ sels v = refl

-- ○⟪⟫ⁿ∘++

○⟪⟫ⁿ∘++ : (nt : NTrm) (sels1 sels2 : List Selector) →
  nt ○⟪ sels1 ++ sels2 ⟫ⁿ ≡
  nt ○⟪ sels2 ⟫ⁿ ○⟪ sels1 ⟫ⁿ

○⟪⟫ⁿ∘++ []ⁿ sels1 sels2 = refl

○⟪⟫ⁿ∘++ (nt1 ∷ⁿ nt2) sels1 sels2 =
  begin
    (nt1 ○⟪ sels1 ++ sels2 ⟫ⁿ) ∷ⁿ (nt2 ○⟪ sels1 ++ sels2 ⟫ⁿ)
    ≡⟨ cong (_∷ⁿ_ (nt1 ○⟪ sels1 ++ sels2 ⟫ⁿ))
            (○⟪⟫ⁿ∘++ nt2 sels1 sels2) ⟩
    (nt1 ○⟪ sels1 ++ sels2 ⟫ⁿ) ∷ⁿ (nt2 ○⟪ sels2 ⟫ⁿ ○⟪ sels1 ⟫ⁿ)
    ≡⟨ cong (flip _∷ⁿ_ (nt2 ○⟪ sels2 ⟫ⁿ ○⟪ sels1 ⟫ⁿ))
            (○⟪⟫ⁿ∘++ nt1 sels1 sels2) ⟩
    (nt1 ○⟪ sels2 ⟫ⁿ ○⟪ sels1 ⟫ⁿ) ∷ⁿ (nt2 ○⟪ sels2 ⟫ⁿ ○⟪ sels1 ⟫ⁿ)
  ∎

○⟪⟫ⁿ∘++ ⟪ sels ⟫ⁿ sels1 sels2
  rewrite LM.assoc sels1 sels2 sels
  =  refl

○⟪⟫ⁿ∘++ (IfNilⁿ sels nt1 nt2) sels1 sels2
  rewrite LM.assoc sels1 sels2 sels
        | ○⟪⟫ⁿ∘++ nt1 sels1 sels2
        | ○⟪⟫ⁿ∘++ nt2 sels1 sels2
  = refl

○⟪⟫ⁿ∘++  ↯ⁿ sels1 sels2 = refl

--
-- Simplification of IfNilⁿ
--

-- IfNilⁿ⟱

IfNilⁿ⟱ : (nt0 nt1 nt2 : NTrm) → NTrm

IfNilⁿ⟱ []ⁿ nt1 nt2 =
  nt1
IfNilⁿ⟱ (nt' ∷ⁿ nt'') nt1 nt2 =
  nt2
IfNilⁿ⟱ ⟪ sels ⟫ⁿ nt1 nt2 =
  IfNilⁿ sels nt1 nt2
IfNilⁿ⟱ (IfNilⁿ sels nt' nt'') nt1 nt2 =
  IfNilⁿ sels (IfNilⁿ⟱ nt' nt1 nt2) (IfNilⁿ⟱ nt'' nt1 nt2)
IfNilⁿ⟱ ↯ⁿ nt1 nt2 =
  ↯ⁿ

-- IfNilⁿ⟱ is correct with respect to ifNil

-- ⟦⌈⌉⟧∘IfNilⁿ⟱

⟦⌈⌉⟧∘IfNilⁿ⟱ : ∀ (nt1 nt2 nt3 : NTrm) (v : Val) →
  ⟦⌈ (IfNilⁿ⟱ nt1 nt2 nt3) ⌉⟧ v ≡
    ifNil (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt2 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)

⟦⌈⌉⟧∘IfNilⁿ⟱ []ⁿ nt2 nt3 v = refl
⟦⌈⌉⟧∘IfNilⁿ⟱ (nt' ∷ⁿ nt'') nt2 nt3 v = refl
⟦⌈⌉⟧∘IfNilⁿ⟱ ⟪ sels ⟫ⁿ nt2 nt3 v
  with ⟦ ⟪ sels ⟫ ⟧ v
... | []ˣ = refl
... | v1 ∷ˣ v2 = refl
... | ↯ˣ = refl
⟦⌈⌉⟧∘IfNilⁿ⟱ (IfNilⁿ sels nt' nt'') nt2 nt3 v
  with ⟦ ⟪ sels ⟫ ⟧ v
... | []ˣ      rewrite ⟦⌈⌉⟧∘IfNilⁿ⟱ nt'  nt2 nt3 v = refl
... | v1 ∷ˣ v2 rewrite ⟦⌈⌉⟧∘IfNilⁿ⟱ nt'' nt2 nt3 v = refl
... | ↯ˣ = refl
⟦⌈⌉⟧∘IfNilⁿ⟱ ↯ⁿ nt2 nt3 v = refl

--
-- Symbolic composition of two normal terms.
--

-- _○_

_○_ : NTrm → NTrm → NTrm

[]ⁿ ○ nt2 =
  []ⁿ

nt' ∷ⁿ nt'' ○ nt2 =
  (nt' ○ nt2) ∷ⁿ (nt'' ○ nt2)

⟪ sels ⟫ⁿ ○ nt2 =
  nt2 !!ⁿ sels

IfNilⁿ sels nt' nt'' ○ ⟪ sels2 ⟫ⁿ =
  IfNilⁿ (sels2 ++ sels) (nt' ○⟪ sels2 ⟫ⁿ) (nt'' ○⟪ sels2 ⟫ⁿ)

IfNilⁿ sels nt' nt'' ○ IfNilⁿ sels2 nt2' nt2'' =
  IfNilⁿ sels2 (IfNilⁿ sels nt' nt'' ○ nt2')
               (IfNilⁿ sels nt' nt'' ○ nt2'')

IfNilⁿ sels nt' nt'' ○ nt2 =
  IfNilⁿ⟱ (nt2 !!ⁿ sels) (nt' ○ nt2) (nt'' ○ nt2)

↯ⁿ ○ nt2 =
  ↯ⁿ

-- ○∘IfNilⁿ

○∘IfNilⁿ : (sels1 sels2 : List Selector) →
  (nt1-1 nt1-2 nt2-1 nt2-2 : NTrm) →
  let nt1 = IfNilⁿ sels1 nt1-1 nt1-2 in 
  nt1 ○ IfNilⁿ sels2 nt2-1 nt2-2
    ≡ IfNilⁿ sels2 (nt1 ○ nt2-1) (nt1 ○ nt2-2)

○∘IfNilⁿ sels1 sels2 nt1-1 nt1-2 nt2-1 nt2-2 = refl


--  _○_ is correct with respect to _∘_

-- ⟦⌈⌉⟧∘○

⟦⌈⌉⟧∘○ : (nt1 nt2 : NTrm) (v : Val) →
  ⟦⌈ nt1 ○ nt2 ⌉⟧ v ≡ (⟦⌈ nt1 ⌉⟧ ∘ ⟦⌈ nt2 ⌉⟧) v

⟦⌈⌉⟧∘○ []ⁿ nt2 v =
  refl

⟦⌈⌉⟧∘○ (nt' ∷ⁿ nt'') nt2 v
  rewrite ⟦⌈⌉⟧∘○ nt' nt2 v
        | ⟦⌈⌉⟧∘○ nt'' nt2 v
  = refl

⟦⌈⌉⟧∘○ (⟪ sels ⟫ⁿ) nt2 v =
  begin
    ⟦⌈ ⟪ sels ⟫ⁿ ○ nt2 ⌉⟧ v
      ≡⟨ refl ⟩
    ⟦⌈ nt2 !!ⁿ sels ⌉⟧ v
      ≡⟨ ⟦⌈⌉⟧∘!!ⁿ nt2 sels v ⟩
    (⟦ ⌈ nt2 ⌉ ⟧ v) !! sels
      ≡⟨ sym $ ⟦⟧∘⟪⟫ sels (⟦ ⌈ nt2 ⌉ ⟧ v) ⟩
    ⟦ ⟪ sels ⟫ ⟧ (⟦ ⌈ nt2 ⌉ ⟧ v)
      ≡⟨ refl ⟩
    ⟦⌈ ⟪ sels ⟫ⁿ ⌉⟧ (⟦⌈ nt2 ⌉⟧ v)
  ∎

⟦⌈⌉⟧∘○ (IfNilⁿ sels nt' nt'') nt2 v =
  begin
    ⟦⌈ IfNilⁿ sels nt' nt'' ○ nt2 ⌉⟧ v
      ≡⟨ helper nt2 ⟩
    ifNil (⟦⌈ nt2 !!ⁿ sels ⌉⟧ v)
          (⟦⌈ nt' ○ nt2 ⌉⟧ v) (⟦⌈ nt'' ○ nt2 ⌉⟧ v)
      ≡⟨ ifNil-cong (⟦⌈⌉⟧∘!!ⁿ nt2 sels v) refl refl ⟩
    ifNil (⟦⌈ nt2 ⌉⟧ v !! sels)
          (⟦⌈ nt' ○ nt2 ⌉⟧ v) (⟦⌈ nt'' ○ nt2 ⌉⟧ v)
      ≡⟨ ifNil-cong (sym $
           ⟦⟧∘⟪⟫ sels (⟦ ⌈ nt2 ⌉ ⟧ v))
           (⟦⌈⌉⟧∘○ nt' nt2 v)
           (⟦⌈⌉⟧∘○ nt'' nt2 v) ⟩
    ifNil (⟦ ⟪ sels ⟫ ⟧ (⟦⌈ nt2 ⌉⟧ v))
          (⟦⌈ nt' ⌉⟧ (⟦⌈ nt2 ⌉⟧ v)) (⟦⌈ nt'' ⌉⟧(⟦⌈ nt2 ⌉⟧ v))
      ≡⟨ refl ⟩
    ⟦⌈ IfNilⁿ sels nt' nt'' ⌉⟧ (⟦⌈ nt2 ⌉⟧ v)
  ∎
  where
    helper : (nt2 : NTrm) →
      ⟦⌈ IfNilⁿ sels nt' nt'' ○ nt2 ⌉⟧ v
      ≡
      ifNil (⟦⌈ nt2 !!ⁿ sels ⌉⟧ v)
            (⟦⌈ nt' ○ nt2 ⌉⟧ v) (⟦⌈ nt'' ○ nt2 ⌉⟧ v)

    helper ⟪ sels' ⟫ⁿ = begin
      ⟦⌈ IfNilⁿ sels nt' nt'' ○ ⟪ sels' ⟫ⁿ ⌉⟧ v
        ≡⟨ refl ⟩
      ifNil (⟦ ⟪ sels' ++ sels ⟫ ⟧ v)
            (⟦⌈ nt' ○⟪ sels' ⟫ⁿ ⌉⟧ v) (⟦⌈ nt'' ○⟪ sels' ⟫ⁿ ⌉⟧ v)
        ≡⟨ ifNil-cong (⟦⟧∘⟪⟫ (sels' ++ sels) v)
                      (⟦⌈⌉⟧∘○⟪⟫ⁿ nt' sels' v)
                      (⟦⌈⌉⟧∘○⟪⟫ⁿ nt'' sels' v) ⟩
      ifNil (v !! (sels' ++ sels))
            (⟦⌈ nt' ⌉⟧ (v !! sels')) (⟦⌈ nt'' ⌉⟧ (v !! sels'))
        ≡⟨ ifNil-cong
            (!!∘++ v sels' sels)
            (sym $ cong (⟦ ⌈ nt' ⌉ ⟧) (⟦⟧∘⟪⟫ sels' v))
            (sym $ cong (⟦ ⌈ nt'' ⌉ ⟧) (⟦⟧∘⟪⟫ sels' v)) ⟩
      ifNil (v !! sels' !! sels)
            (⟦⌈ nt' ⌉⟧ (⟦⌈ ⟪ sels' ⟫ⁿ ⌉⟧ v))
            (⟦⌈ nt'' ⌉⟧ (⟦⌈ ⟪ sels' ⟫ⁿ ⌉⟧ v))
        ≡⟨ ifNil-cong
             (cong (flip _!!_ sels) (sym (⟦⟧∘⟪⟫ sels' v)))
             (sym $ ⟦⌈⌉⟧∘○ nt' ⟪ sels' ⟫ⁿ v)
             (sym $ ⟦⌈⌉⟧∘○ nt'' ⟪ sels' ⟫ⁿ v) ⟩
      ifNil (⟦ ⟪ sels' ⟫ ⟧ v !! sels)
            (⟦⌈ nt' ○ ⟪ sels' ⟫ⁿ ⌉⟧ v)
            (⟦⌈ nt'' ○ ⟪ sels' ⟫ⁿ ⌉⟧ v)
        ≡⟨ refl ⟩
      ifNil (⟦⌈ ⟪ sels' ⟫ⁿ ⌉⟧ v !! sels)
            (⟦⌈ nt' ○ ⟪ sels' ⟫ⁿ ⌉⟧ v)
            (⟦⌈ nt'' ○ ⟪ sels' ⟫ⁿ ⌉⟧ v)
        ≡⟨ ifNil-cong
             (sym (⟦⌈⌉⟧∘!!ⁿ ⟪ sels' ⟫ⁿ sels v))
             refl refl ⟩
      ifNil (⟦⌈ ⟪ sels' ⟫ⁿ !!ⁿ sels ⌉⟧ v)
            (⟦⌈ nt' ○ ⟪ sels' ⟫ⁿ ⌉⟧ v)
            (⟦⌈ nt'' ○ ⟪ sels' ⟫ⁿ ⌉⟧ v)
      ∎

    helper (IfNilⁿ sels' nt1 nt3) = begin
      ⟦⌈ IfNilⁿ sels nt' nt'' ○ IfNilⁿ sels' nt1 nt3 ⌉⟧ v
        ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
                (○∘IfNilⁿ sels sels' nt' nt'' nt1 nt3) ⟩
      ⟦⌈ IfNilⁿ sels'
                (IfNilⁿ sels nt' nt'' ○ nt1)
                (IfNilⁿ sels nt' nt'' ○ nt3) ⌉⟧ v
        ≡⟨ refl ⟩
      ifNil (⟦ ⟪ sels' ⟫ ⟧ v)
            (⟦⌈ IfNilⁿ sels nt' nt'' ○ nt1 ⌉⟧ v)
            (⟦⌈ IfNilⁿ sels nt' nt'' ○ nt3 ⌉⟧ v)
        ≡⟨ ifNil-cong
             (⟦⟧∘⟪⟫ sels' v)
             (⟦⌈⌉⟧∘○ (IfNilⁿ sels nt' nt'') nt1 v)
             (⟦⌈⌉⟧∘○ (IfNilⁿ sels nt' nt'') nt3 v) ⟩
      ifNil (v !! sels')
        (⟦⌈ IfNilⁿ sels nt' nt'' ⌉⟧ (⟦⌈ nt1 ⌉⟧ v))
        (⟦⌈ IfNilⁿ sels nt' nt'' ⌉⟧ (⟦⌈ nt3 ⌉⟧ v))
        ≡⟨ refl ⟩
      ifNil (v !! sels')
        (ifNil (⟦ ⟪ sels ⟫ ⟧ (⟦⌈ nt1 ⌉⟧ v))
               (⟦⌈ nt' ⌉⟧ (⟦⌈ nt1 ⌉⟧ v))
               (⟦⌈ nt'' ⌉⟧ (⟦⌈ nt1 ⌉⟧ v)))
        (ifNil (⟦ ⟪ sels ⟫ ⟧ (⟦⌈ nt3 ⌉⟧ v))
               (⟦⌈ nt' ⌉⟧ (⟦⌈ nt3 ⌉⟧ v))
               (⟦⌈ nt'' ⌉⟧ (⟦⌈ nt3 ⌉⟧ v)))
        ≡⟨ cong₂ (ifNil (v !! sels'))
                 (ifNil-cong (⟦⟧∘⟪⟫ sels (⟦⌈ nt1 ⌉⟧ v)) refl refl)
                 (ifNil-cong (⟦⟧∘⟪⟫ sels (⟦⌈ nt3 ⌉⟧ v)) refl refl) ⟩
      ifNil (v !! sels')
        (ifNil (⟦⌈ nt1 ⌉⟧ v !! sels)
               (⟦⌈ nt' ⌉⟧ (⟦⌈ nt1 ⌉⟧ v))
               (⟦⌈ nt'' ⌉⟧ (⟦⌈ nt1 ⌉⟧ v)))
        (ifNil (⟦⌈ nt3 ⌉⟧ v !! sels)
               (⟦⌈ nt' ⌉⟧ (⟦⌈ nt3 ⌉⟧ v))
               (⟦⌈ nt'' ⌉⟧ (⟦⌈ nt3 ⌉⟧ v)))
        ≡⟨ helper₂ (v !! sels')
                   (⟦⌈ nt1 ⌉⟧ v !! sels)
                   (⟦⌈ nt3 ⌉⟧ v !! sels)
                   ⟦⌈ nt' ⌉⟧ ⟦⌈ nt'' ⌉⟧
                   (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v) ⟩
      ifNil (v !! sels')
            (ifNil (⟦⌈ nt1 ⌉⟧ v !! sels)
                   (⟦⌈ nt' ⌉⟧ (ifNil (v !! sels')
                                     (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
                   (⟦⌈ nt'' ⌉⟧ (ifNil (v !! sels')
                                      (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v))))
            (ifNil (⟦⌈ nt3 ⌉⟧ v !! sels)
                   (⟦⌈ nt' ⌉⟧ (ifNil (v !! sels')
                                     (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
                   (⟦⌈ nt'' ⌉⟧ (ifNil (v !! sels')
                                      (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v))))
        ≡⟨ sym $ ifNil∘ifNil (v !! sels') ⟩
      ifNil (ifNil (v !! sels')
                   (⟦⌈ nt1 ⌉⟧ v !! sels)
                   (⟦⌈ nt3 ⌉⟧ v !! sels))
            (⟦⌈ nt' ⌉⟧ (ifNil (v !! sels')
                              (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
            (⟦⌈ nt'' ⌉⟧ (ifNil (v !! sels')
                               (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
        ≡⟨ ifNil-cong (sym $ !!∘ifNil (v !! sels') sels) refl refl ⟩
      ifNil (ifNil (v !! sels') (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v) !! sels)
            (⟦⌈ nt' ⌉⟧ (ifNil (v !! sels') (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
            (⟦⌈ nt'' ⌉⟧ (ifNil (v !! sels') (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
        ≡⟨ ifNil-cong
             (cong (flip _!!_ sels)
                   (ifNil-cong (sym $ ⟦⟧∘⟪⟫ sels' v) refl refl))
             (cong ⟦⌈ nt' ⌉⟧
                   (ifNil-cong (sym $ ⟦⟧∘⟪⟫ sels' v) refl refl))
             (cong ⟦⌈ nt'' ⌉⟧
                   (ifNil-cong (sym $ ⟦⟧∘⟪⟫ sels' v) refl refl)) ⟩
      ifNil (ifNil (⟦ ⟪ sels' ⟫ ⟧ v)
                   (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v) !! sels)
            (⟦⌈ nt' ⌉⟧ (ifNil (⟦ ⟪ sels' ⟫ ⟧ v)
                              (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
            (⟦⌈ nt'' ⌉⟧ (ifNil (⟦ ⟪ sels' ⟫ ⟧ v)
                               (⟦⌈ nt1 ⌉⟧ v) (⟦⌈ nt3 ⌉⟧ v)))
        ≡⟨ refl ⟩
      ifNil (⟦⌈ IfNilⁿ sels' nt1 nt3 ⌉⟧ v !! sels)
            (⟦⌈ nt' ⌉⟧ (⟦⌈ IfNilⁿ sels' nt1 nt3 ⌉⟧ v))
            (⟦⌈ nt'' ⌉⟧ (⟦⌈ IfNilⁿ sels' nt1 nt3 ⌉⟧ v))
        ≡⟨ ifNil-cong
             (sym $ ⟦⌈⌉⟧∘!!ⁿ (IfNilⁿ sels' nt1 nt3) sels v)
             (sym $ ⟦⌈⌉⟧∘○ nt' (IfNilⁿ sels' nt1 nt3) v)
             (sym $ ⟦⌈⌉⟧∘○ nt'' (IfNilⁿ sels' nt1 nt3) v) ⟩
      ifNil (⟦⌈ IfNilⁿ sels' nt1 nt3 !!ⁿ sels ⌉⟧ v)
            (⟦⌈ nt' ○ IfNilⁿ sels' nt1 nt3 ⌉⟧ v)
            (⟦⌈ nt'' ○ (IfNilⁿ sels' nt1 nt3) ⌉⟧ v)
      ∎
      where
        helper₂ : ∀ w (u1 u3 : Val) (f1 f2 : Val → Val) (v1 v3 : Val) →
          ifNil w (ifNil u1 (f1 v1) (f2 v1))
                  (ifNil u3 (f1 v3) (f2 v3))
          ≡
          ifNil w (ifNil u1 (f1 (ifNil w v1 v3)) (f2 (ifNil w v1 v3)))
                  (ifNil u3 (f1 (ifNil w v1 v3)) (f2 (ifNil w v1 v3)))
        helper₂ []ˣ        u1 u3 f1 f2 v1 v3 = refl
        helper₂ (_ ∷ˣ _) u1 u3 f1 f2 v1 v3 = refl
        helper₂ ↯ˣ     u1 u3 f1 f2 v1 v3 = refl

    helper []ⁿ = begin
      ⟦⌈ IfNilⁿ sels nt' nt'' ○ []ⁿ ⌉⟧ v
        ≡⟨ refl ⟩
      ⟦⌈ IfNilⁿ⟱ ([]ⁿ !!ⁿ sels) (nt' ○ []ⁿ) (nt'' ○ []ⁿ) ⌉⟧ v
        ≡⟨ ⟦⌈⌉⟧∘IfNilⁿ⟱ ([]ⁿ !!ⁿ sels) (nt' ○ []ⁿ) (nt'' ○ []ⁿ) v ⟩
      ifNil (⟦⌈ []ⁿ !!ⁿ sels ⌉⟧ v)
            (⟦⌈ nt' ○ []ⁿ ⌉⟧ v) (⟦⌈ nt'' ○ []ⁿ ⌉⟧ v)
      ∎

    helper (nt1 ∷ⁿ nt3) = begin
      ⟦⌈ IfNilⁿ sels nt' nt'' ○ nt1 ∷ⁿ nt3 ⌉⟧ v
        ≡⟨ refl ⟩
      ⟦⌈ IfNilⁿ⟱ (nt1 ∷ⁿ nt3 !!ⁿ sels)
                 (nt' ○ nt1 ∷ⁿ nt3) (nt'' ○ nt1 ∷ⁿ nt3) ⌉⟧ v
        ≡⟨ ⟦⌈⌉⟧∘IfNilⁿ⟱
             (nt1 ∷ⁿ nt3 !!ⁿ sels)
             (nt' ○ nt1 ∷ⁿ nt3) (nt'' ○ nt1 ∷ⁿ nt3) v ⟩
      ifNil (⟦⌈ nt1 ∷ⁿ nt3 !!ⁿ sels ⌉⟧ v)
            (⟦⌈ nt' ○ nt1 ∷ⁿ nt3 ⌉⟧ v)
            (⟦⌈ nt'' ○ nt1 ∷ⁿ nt3 ⌉⟧ v)
      ∎

    helper ↯ⁿ = begin
      ⟦⌈ IfNilⁿ sels nt' nt'' ○ ↯ⁿ ⌉⟧ v
        ≡⟨ refl ⟩
      ⟦⌈ IfNilⁿ⟱ (↯ⁿ !!ⁿ sels)
                 (nt' ○ ↯ⁿ) (nt'' ○ ↯ⁿ) ⌉⟧ v
        ≡⟨ ⟦⌈⌉⟧∘IfNilⁿ⟱ (↯ⁿ !!ⁿ sels) (nt' ○ ↯ⁿ) (nt'' ○ ↯ⁿ) v ⟩
      ifNil (⟦⌈ ↯ⁿ !!ⁿ sels ⌉⟧ v)
            (⟦⌈ nt' ○ ↯ⁿ ⌉⟧ v)
            (⟦⌈ nt'' ○ ↯ⁿ ⌉⟧ v)
      ∎

⟦⌈⌉⟧∘○ ↯ⁿ nt2 v =
  refl

---------------------------
-- Normalization of terms!
---------------------------

-- ⌋_⌊ not only brings expressions into normal form,
-- but also achieves some optimizations like deforestation.

-- ⌋_⌊

⌋_⌊ : (t : Trm) → NTrm

⌋ [] ⌊ = []ⁿ
⌋ t1 ∷ t2 ⌊ = ⌋ t1 ⌊  ∷ⁿ ⌋ t2 ⌊
⌋ Hd ⌊ = ⟪ [ HD ] ⟫ⁿ
⌋ Tl ⌊ = ⟪ [ TL ] ⟫ⁿ
⌋ Id ⌊ = ⟪ [] ⟫ⁿ
⌋ t1 $$ t2 ⌊ = ⌋ t1 ⌊ ○ ⌋ t2 ⌊
⌋ IfNil t0 t1 t2 ⌊ = IfNilⁿ⟱ ⌋ t0 ⌊ ⌋ t1 ⌊ ⌋ t2 ⌊
⌋ ↯ ⌊ = ↯ⁿ

------------------------------------------------------------------
-- The main theorem establishing the correctness of normalization.
------------------------------------------------------------------

-- ⟦⌈⌉⟧∘⌋⌊

⟦⌈⌉⟧∘⌋⌊ : (t : Trm) (v : Val) →
  ⟦⌈ ⌋ t ⌊ ⌉⟧ v ≡ ⟦ t ⟧ v

⟦⌈⌉⟧∘⌋⌊ [] v =
  refl
⟦⌈⌉⟧∘⌋⌊ (t1 ∷ t2) v
  rewrite ⟦⌈⌉⟧∘⌋⌊ t1 v | ⟦⌈⌉⟧∘⌋⌊ t2 v
  = refl
⟦⌈⌉⟧∘⌋⌊ Hd v =
  refl
⟦⌈⌉⟧∘⌋⌊ Tl v =
  refl
⟦⌈⌉⟧∘⌋⌊ Id v =
  refl
⟦⌈⌉⟧∘⌋⌊ (t1 $$ t2) v = begin
  ⟦⌈ ⌋ t1 $$ t2 ⌊ ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ ⌋ t1 ⌊ ○ ⌋ t2 ⌊ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○ ⌋ t1 ⌊ ⌋ t2 ⌊ v ⟩
  ⟦⌈ ⌋ t1 ⌊ ⌉⟧ (⟦⌈ ⌋ t2 ⌊ ⌉⟧ v)
    ≡⟨ cong ⟦⌈ ⌋ t1 ⌊ ⌉⟧ (⟦⌈⌉⟧∘⌋⌊ t2 v) ⟩
  ⟦⌈ ⌋ t1 ⌊ ⌉⟧ (⟦ t2 ⟧ v)
    ≡⟨ ⟦⌈⌉⟧∘⌋⌊ t1 (⟦ t2 ⟧ v) ⟩
  ⟦ t1 ⟧ (⟦ t2 ⟧ v)
    ≡⟨ refl ⟩
  ⟦ t1 $$ t2 ⟧ v
  ∎
⟦⌈⌉⟧∘⌋⌊ (IfNil t0 t1 t2) v = begin
  ⟦⌈ ⌋ IfNil t0 t1 t2 ⌊ ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ IfNilⁿ⟱ ⌋ t0 ⌊ ⌋ t1 ⌊ ⌋ t2 ⌊ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘IfNilⁿ⟱ ⌋ t0 ⌊ ⌋ t1 ⌊ ⌋ t2 ⌊ v ⟩
  ifNil (⟦⌈ ⌋ t0 ⌊ ⌉⟧ v)
        (⟦⌈ ⌋ t1 ⌊ ⌉⟧ v) (⟦⌈ ⌋ t2 ⌊ ⌉⟧ v)
    ≡⟨ ifNil-cong (⟦⌈⌉⟧∘⌋⌊ t0 v)
                  (⟦⌈⌉⟧∘⌋⌊ t1 v) (⟦⌈⌉⟧∘⌋⌊ t2 v) ⟩
  ifNil (⟦ t0 ⟧ v) (⟦ t1 ⟧ v) (⟦ t2 ⟧ v)
    ≡⟨ refl ⟩
  ⟦ IfNil t0 t1 t2 ⟧ v
  ∎
⟦⌈⌉⟧∘⌋⌊ ↯ v =
  refl

---------------------------
-- Emulating substitutions
---------------------------

-- Substitutions can be emulated inside our language, giving
-- a simple form of "explicit substitutions".

-- We define t [ sels ]≔ⁿ t′ , which, for a given position `sels` in t
-- generates a new normal-form term, such that
--     ⟦⌈ t [ sels ]≔ⁿ t′ ⌉⟧ v ≡ (⟦⌈ t ⌉⟧ v) [ sels ]≔ (⟦⌈ t′ ⌉⟧ v)

-- _[_]≔ⁿ_

infixl 6 _[_]≔ⁿ_

_[_]≔ⁿ_ : (t : NTrm) (sels : List Selector) (t′ : NTrm) → NTrm

t [ [] ]≔ⁿ t′ = t′
t [ HD ∷ sels ]≔ⁿ t′ =
  (t !ⁿ HD) [ sels ]≔ⁿ t′ ∷ⁿ (t !ⁿ TL)
t [ TL ∷ sels ]≔ⁿ t′ =
  (t !ⁿ HD) ∷ⁿ (t !ⁿ TL) [ sels ]≔ⁿ t′

-- _[_]≔ⁿ_ is correct with respect to _[_]≔_

-- ⟦⟧∘[]≔ⁿ

⟦⟧∘[]≔ⁿ : ∀ (sels : List Selector) t t′ (v v′ : Val) →
  ⟦⌈ t [ sels ]≔ⁿ t′ ⌉⟧ v ≡ (⟦⌈ t ⌉⟧ v) [ sels ]≔ (⟦⌈ t′ ⌉⟧ v) 

⟦⟧∘[]≔ⁿ [] t t′ v v′ = refl

⟦⟧∘[]≔ⁿ (HD ∷ sels) t t′ v v′ =
  begin
    ⟦⌈ (t !ⁿ HD) [ sels ]≔ⁿ t′ ⌉⟧ v ∷ˣ ⟦⌈ t !ⁿ TL ⌉⟧ v
      ≡⟨ cong (flip _∷ˣ_ (⟦ ⌈ t !ⁿ TL ⌉ ⟧ v))
                         (⟦⟧∘[]≔ⁿ sels (t !ⁿ HD) t′ v v′) ⟩
    ⟦⌈ t !ⁿ HD ⌉⟧ v [ sels ]≔ ⟦ ⌈ t′ ⌉ ⟧ v ∷ˣ ⟦⌈ t !ⁿ TL ⌉⟧ v
      ≡⟨ cong₂ _∷ˣ_ (cong₂ (flip _[_]≔_ sels) (⟦⌈⌉⟧∘!ⁿ t HD v) refl)
                    (⟦⌈⌉⟧∘!ⁿ t TL v) ⟩
    (⟦⌈ t ⌉⟧ v ! HD) [ sels ]≔ ⟦⌈ t′ ⌉⟧ v ∷ˣ (⟦⌈ t ⌉⟧ v ! TL)
  ∎

⟦⟧∘[]≔ⁿ (TL ∷ sels) t t′ v v′ =
  begin
    ⟦⌈ t !ⁿ HD ⌉⟧ v ∷ˣ ⟦⌈ (t !ⁿ TL) [ sels ]≔ⁿ t′ ⌉⟧ v
      ≡⟨ cong (_∷ˣ_ (⟦ ⌈ t !ⁿ HD ⌉ ⟧ v))
                    (⟦⟧∘[]≔ⁿ sels (t !ⁿ TL) t′ v v′) ⟩
    ⟦⌈ t !ⁿ HD ⌉⟧ v ∷ˣ ⟦⌈ t !ⁿ TL ⌉⟧ v [ sels ]≔ ⟦⌈ t′ ⌉⟧ v
      ≡⟨ cong₂ _∷ˣ_ (⟦⌈⌉⟧∘!ⁿ t HD v)
                    (cong₂ (flip _[_]≔_ sels) (⟦⌈⌉⟧∘!ⁿ t TL v) refl) ⟩
    (⟦⌈ t ⌉⟧ v ! HD) ∷ˣ (⟦⌈ t ⌉⟧ v ! TL) [ sels ]≔ ⟦⌈ t′ ⌉⟧ v
  ∎

-- !!ⁿ∘[]≔ⁿ-id

!!ⁿ∘[]≔ⁿ-id : (sels : List Selector) (t t′ : NTrm) →
  t [ sels ]≔ⁿ t′ !!ⁿ sels ≡ t′

!!ⁿ∘[]≔ⁿ-id [] t t′ = refl
!!ⁿ∘[]≔ⁿ-id (HD ∷ sels) t t′ = begin
  t [ HD ∷ sels ]≔ⁿ t′ !!ⁿ HD ∷ sels
    ≡⟨ refl ⟩
  (t !ⁿ HD) [ sels ]≔ⁿ t′ !!ⁿ sels
    ≡⟨ !!ⁿ∘[]≔ⁿ-id sels (t !ⁿ HD) t′ ⟩
  t′
  ∎
!!ⁿ∘[]≔ⁿ-id (TL ∷ sels) t t′ = begin
  t [ TL ∷ sels ]≔ⁿ t′ !!ⁿ (TL ∷ sels)
    ≡⟨ refl ⟩
  (t !ⁿ TL) [ sels ]≔ⁿ t′ !!ⁿ sels
    ≡⟨ !!ⁿ∘[]≔ⁿ-id sels (t !ⁿ TL) t′ ⟩
  t′
  ∎

-- []≔ⁿ∘++

[]≔ⁿ∘++ : ∀ (sels1 sels2 : List Selector) (nt nt′ : NTrm) →
  nt [ sels1 ++ sels2 ]≔ⁿ nt′
  ≡
  nt [ sels1 ]≔ⁿ ((nt !!ⁿ sels1) [ sels2 ]≔ⁿ nt′)

[]≔ⁿ∘++ [] sels2 nt nt′ = refl
[]≔ⁿ∘++ (HD ∷ sels1) sels2 nt nt′ = begin
  nt [ (HD ∷ sels1) ++ sels2 ]≔ⁿ nt′
    ≡⟨ refl ⟩
  (nt !ⁿ HD) [ sels1 ++ sels2 ]≔ⁿ nt′ ∷ⁿ (nt !ⁿ TL)
    ≡⟨ cong (flip _∷ⁿ_ (nt !ⁿ TL))
            ([]≔ⁿ∘++ sels1 sels2 (nt !ⁿ HD) nt′) ⟩
  (nt !ⁿ HD) [ sels1 ]≔ⁿ ((nt !ⁿ HD !!ⁿ sels1) [ sels2 ]≔ⁿ nt′) ∷ⁿ (nt !ⁿ TL)
    ≡⟨ refl ⟩
  nt [ HD ∷ sels1 ]≔ⁿ ((nt !!ⁿ HD ∷ sels1) [ sels2 ]≔ⁿ nt′)
  ∎
[]≔ⁿ∘++ (TL ∷ sels1) sels2 nt nt′ =
  cong (_∷ⁿ_ (nt !ⁿ HD))
       ([]≔ⁿ∘++ sels1 sels2 (nt !ⁿ TL) nt′)

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

-- !!ⁿ∘[]≔ⁿ∘++

!!ⁿ∘[]≔ⁿ∘++ :
  ∀ (ws us vs : List Selector) (nt nt′ : NTrm) →
    nt [ ws ++ vs ]≔ⁿ nt′ !!ⁿ ws ++ us
      ≡ (nt !!ⁿ ws) [ vs ]≔ⁿ nt′ !!ⁿ us

!!ⁿ∘[]≔ⁿ∘++ [] us vs nt nt′ = refl
!!ⁿ∘[]≔ⁿ∘++ (HD ∷ ws) us vs nt nt′ =
  !!ⁿ∘[]≔ⁿ∘++ ws us vs (nt !ⁿ HD) nt′
!!ⁿ∘[]≔ⁿ∘++ (TL ∷ ws) us vs nt nt′ =
  !!ⁿ∘[]≔ⁿ∘++ ws us vs (nt !ⁿ TL) nt′

-- !!ⁿ∘[]≔ⁿ-prefix

!!ⁿ∘[]≔ⁿ-prefix :
  ∀ (sels1 sels2 : List Selector) (nt nt′ : NTrm) →
    let cp = commonPrefix? _≟Sel_ sels1 sels2
        ws = proj₁ cp
        us = proj₁ (proj₂ cp)
        vs = proj₁ (proj₂ (proj₂ cp))
    in nt [ sels2 ]≔ⁿ nt′ !!ⁿ sels1
       ≡ (nt !!ⁿ ws) [ vs ]≔ⁿ nt′ !!ⁿ us

!!ⁿ∘[]≔ⁿ-prefix sels1 sels2 nt nt′ with commonPrefix? _≟Sel_ sels1 sels2
... | ws , us , vs , sels1≡ws++us , sels2≡ws++vs
  rewrite sels1≡ws++us | sels2≡ws++vs =
  !!ⁿ∘[]≔ⁿ∘++ ws us vs nt nt′


-- []≔ⁿ∘⟪⟫ⁿ

[]≔ⁿ∘⟪⟫ⁿ : (sels1 sels2 : List Selector) (nt : NTrm) →
  ⟪ sels2 ⟫ⁿ [ sels1 ]≔ⁿ nt 
    ≡ ⟪ [] ⟫ⁿ [ sels2 ++ sels1 ]≔ⁿ nt !!ⁿ sels2

[]≔ⁿ∘⟪⟫ⁿ sels1 sels2 nt =
  begin
    ⟪ sels2 ⟫ⁿ [ sels1 ]≔ⁿ nt
      ≡⟨ refl ⟩
    ⟪ sels2 ⟫ⁿ [ sels1 ]≔ⁿ nt !!ⁿ []
      ≡⟨ cong (λ z → z [ sels1 ]≔ⁿ  nt !!ⁿ [])
              (sym $ !!ⁿ∘⟪⟫ⁿ [] sels2) ⟩
    (⟪ [] ⟫ⁿ !!ⁿ sels2) [ sels1 ]≔ⁿ nt !!ⁿ []
      ≡⟨ sym $ !!ⁿ∘[]≔ⁿ-prefix [] sels1 (⟪ [] ⟫ⁿ !!ⁿ sels2) nt ⟩
    (⟪ [] ⟫ⁿ !!ⁿ sels2) [ sels1 ]≔ⁿ nt
      ≡⟨ sym $ !!ⁿ∘[]≔ⁿ∘++ sels2 [] sels1 ⟪ [] ⟫ⁿ nt ⟩
    ⟪ [] ⟫ⁿ [ sels2 ++ sels1 ]≔ⁿ nt !!ⁿ (sels2 ++ [])
      ≡⟨ cong (_!!ⁿ_ (⟪ [] ⟫ⁿ [ sels2 ++ sels1 ]≔ⁿ nt))
              (proj₂ LM.identity sels2) ⟩
    ⟪ [] ⟫ⁿ [ sels2 ++ sels1 ]≔ⁿ nt !!ⁿ sels2
  ∎

--
