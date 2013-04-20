--
-- An injection from simple expressions into first-order terms
--

module SimpExpAsFOT where

open import Data.Empty
open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import ExpLang
open import HomEmb

-- TrmCons
-- (An enumeration of the constructors of expressions.)

data TrmCons : Set where
  TCNil TCCons TCSelHd TCSelTl TCId TCCmp TCIfNil TCBottom
    : TrmCons

-- _≟TC_

_≟TC_ : (t1 t2 : TrmCons) → Dec (t1 ≡ t2)

TCNil ≟TC TCNil = yes refl
TCNil ≟TC TCCons = no (λ ())
TCNil ≟TC TCSelHd = no (λ ())
TCNil ≟TC TCSelTl = no (λ ())
TCNil ≟TC TCId = no (λ ())
TCNil ≟TC TCCmp = no (λ ())
TCNil ≟TC TCIfNil = no (λ ())
TCNil ≟TC TCBottom = no (λ ())
TCCons ≟TC TCNil = no (λ ())
TCCons ≟TC TCCons = yes refl
TCCons ≟TC TCSelHd = no (λ ())
TCCons ≟TC TCSelTl = no (λ ())
TCCons ≟TC TCId = no (λ ())
TCCons ≟TC TCCmp = no (λ ())
TCCons ≟TC TCIfNil = no (λ ())
TCCons ≟TC TCBottom = no (λ ())
TCSelHd ≟TC TCNil = no (λ ())
TCSelHd ≟TC TCCons = no (λ ())
TCSelHd ≟TC TCSelHd = yes refl
TCSelHd ≟TC TCSelTl = no (λ ())
TCSelHd ≟TC TCId = no (λ ())
TCSelHd ≟TC TCCmp = no (λ ())
TCSelHd ≟TC TCIfNil = no (λ ())
TCSelHd ≟TC TCBottom = no (λ ())
TCSelTl ≟TC TCNil = no (λ ())
TCSelTl ≟TC TCCons = no (λ ())
TCSelTl ≟TC TCSelHd = no (λ ())
TCSelTl ≟TC TCSelTl = yes refl
TCSelTl ≟TC TCId = no (λ ())
TCSelTl ≟TC TCCmp = no (λ ())
TCSelTl ≟TC TCIfNil = no (λ ())
TCSelTl ≟TC TCBottom = no (λ ())
TCId ≟TC TCNil = no (λ ())
TCId ≟TC TCCons = no (λ ())
TCId ≟TC TCSelHd = no (λ ())
TCId ≟TC TCSelTl = no (λ ())
TCId ≟TC TCId = yes refl
TCId ≟TC TCCmp = no (λ ())
TCId ≟TC TCIfNil = no (λ ())
TCId ≟TC TCBottom = no (λ ())
TCCmp ≟TC TCNil = no (λ ())
TCCmp ≟TC TCCons = no (λ ())
TCCmp ≟TC TCSelHd = no (λ ())
TCCmp ≟TC TCSelTl = no (λ ())
TCCmp ≟TC TCId = no (λ ())
TCCmp ≟TC TCCmp = yes refl
TCCmp ≟TC TCIfNil = no (λ ())
TCCmp ≟TC TCBottom = no (λ ())
TCIfNil ≟TC TCNil = no (λ ())
TCIfNil ≟TC TCCons = no (λ ())
TCIfNil ≟TC TCSelHd = no (λ ())
TCIfNil ≟TC TCSelTl = no (λ ())
TCIfNil ≟TC TCId = no (λ ())
TCIfNil ≟TC TCCmp = no (λ ())
TCIfNil ≟TC TCIfNil = yes refl
TCIfNil ≟TC TCBottom = no (λ ())
TCBottom ≟TC TCNil = no (λ ())
TCBottom ≟TC TCCons = no (λ ())
TCBottom ≟TC TCSelHd = no (λ ())
TCBottom ≟TC TCSelTl = no (λ ())
TCBottom ≟TC TCId = no (λ ())
TCBottom ≟TC TCCmp = no (λ ())
TCBottom ≟TC TCIfNil = no (λ ())
TCBottom ≟TC TCBottom = yes refl

-- TrmToFOTerm

TrmToFOTerm : (t : Trm) → FOTerm ⊥ TrmCons

TrmToFOTerm [] =
  FOFun0 (just TCNil)
TrmToFOTerm (t1 ∷ t2) =
  FOFun2 (just TCCons) (TrmToFOTerm t1) (TrmToFOTerm t2)
TrmToFOTerm (Sel HD) =
  FOFun0 (just TCSelHd)
TrmToFOTerm (Sel TL) =
  FOFun0 (just TCSelTl)
TrmToFOTerm Id =
  FOFun0 (just TCId)
TrmToFOTerm (t1 $$ t2) =
  FOFun2 (just TCCmp) (TrmToFOTerm t1) (TrmToFOTerm t2)

TrmToFOTerm (IfNil t0 t1 t2) =
  FOFun2 (just TCIfNil) (TrmToFOTerm t0)
         (FOFun2 (just TCCons) (TrmToFOTerm t1) (TrmToFOTerm t2))

TrmToFOTerm Bottom =
  FOFun0 (just TCBottom)

open ⊴-Decidable ⊥ TrmCons _≟TC_ public

--
