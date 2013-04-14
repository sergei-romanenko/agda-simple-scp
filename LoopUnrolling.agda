--
-- A simple form of loop unrolling:
-- trying to execute the body of the loop once before entering the loop,
-- provided the condition of the loop holds.
--

module LoopUnrolling where

open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Data.Empty

open import Function
open import Function.Equivalence
  using (_⇔_; equivalence)


open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; trans; cong; subst; inspect; module ≡-Reasoning)
  renaming ([_] to [_]ⁱ)

import Function.Related as Related

open import Util
open import ExpLang
open import PositiveInfo
open import ImpLang

-- unrollToInit

unrollToInit : KNFProg → KNFProg

unrollToInit (KNF initExp condExp bodyExp finalExp) =
  KNF newInit condExp bodyExp finalExp
  where newInit = ntrm2trm $ norm $ Cmp (IfNil condExp Id bodyExp) initExp

-----------------------------------
-- Unrolling respects the semantics
-----------------------------------

{-
-- ⊨KNF-Bottom

⊨While-Bottom : ∀ {cond e} →
  strictTrm cond →
  [ cond ] e ⊨While VBottom ⇓ VBottom

⊨While-Bottom h = ⇓-WhileBottom h
-}

{-
-- evalKNFCore-Bottom

evalKNFCore-Bottom : ∀ i cond e v →
  strictTrm cond →
  evalKNFCore i cond e VBottom ≡ just v →
  v ≡ VBottom

evalKNFCore-Bottom zero cond e v hs ()

evalKNFCore-Bottom (suc i) cond e v hs h rewrite hs =
  cong (maybe id VBottom) (P.sym h)
-}

-- ⊨While-unrollToInit-fw

⊨While-unrollToInit-fw :
  ∀  {cond e v v′} →
    strictTrm cond →
    [ cond ] e ⊨While v ⇓ v′ →
    [ cond ] e ⊨While evalT (IfNil cond Id e) v ⇓  v′

⊨While-unrollToInit-fw hs (⇓-WhileNil ≡VNil) rewrite ≡VNil =
  ⇓-WhileNil ≡VNil
⊨While-unrollToInit-fw hs (⇓-WhileBottom ≡VBottom) rewrite ≡VBottom =
  ⇓-WhileBottom hs
⊨While-unrollToInit-fw hs (⇓-WhileCons ≡VCons h) rewrite ≡VCons =
  h

⊨While-unrollToInit-bw :
  ∀  {cond e v v′} →
    strictTrm cond →
    [ cond ] e ⊨While evalT (IfNil cond Id e) v ⇓  v′ →
    [ cond ] e ⊨While v ⇓ v′

⊨While-unrollToInit-bw {cond} {e} {v} {v′} hs hw
  with evalT cond v | inspect (evalT cond) v

⊨While-unrollToInit-bw hs hw
  | VNil | [ g ]ⁱ = hw

⊨While-unrollToInit-bw hs hw
  | VCons v1 v2 | [ g ]ⁱ = ⇓-WhileCons g hw

⊨While-unrollToInit-bw hs (⇓-WhileNil ≡VNil)
  | VBottom | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unrollToInit-bw hs (⇓-WhileBottom ≡VBottom)
  | VBottom | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unrollToInit-bw hs (⇓-WhileCons ≡VCons h)
  | VBottom | [ g ]ⁱ =
  ⊥-elim (VCons≢VBottom (trans (P.sym ≡VCons) hs))

{-
evalKNFCore-unrollToInit-fw :
  ∀ i knf v v′ →
    strictTrm (condExp knf) →
    evalKNFCore i (condExp knf) (bodyExp knf) v ≡ just v′ →
    ∃ λ (i′ : ℕ) → evalKNFCore i′ (condExp knf) (bodyExp knf)
      (evalT (IfNil (condExp knf) Id (bodyExp knf)) v) ≡ just v′

evalKNFCore-unrollToInit-fw zero knf v v′ hs ()

--evalKNFCore-unrollToInit-fw (suc i) knf v v′ hs h = {!!}

evalKNFCore-unrollToInit-fw (suc i) knf v v′ hs h
  with evalT (condExp knf) v
... | VNil = {!!}
... | VCons _ _ = {!!}
... | VBottom = i , {!evalKNFCore-Bottom!}
-}

{-
evalKNF-unrollToInit :
  ∀ knf v v′ → strictTrm (condExp knf) →
    (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
    (∃ λ (i′ : ℕ) → evalKNF i′ (unrollToInit knf) v ≡ just v′)

evalKNF-unrollToInit = {!!}
-}

--
