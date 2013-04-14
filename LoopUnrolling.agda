--
-- A simple form of loop unrolling:
-- trying to execute the body of the loop once before entering the loop,
-- provided the condition of the loop holds.
--

module LoopUnrolling where

open import Data.Nat
open import Data.List
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

-- ⊨While-unrollToInit⇒

⊨While-unrollToInit⇒ :
  ∀  {cond e v v′} →
    strictTrm cond →
    [ cond ] e ⊨While v ⇓ v′ →
    [ cond ] e ⊨While evalT (IfNil cond Id e) v ⇓  v′

⊨While-unrollToInit⇒ hs (⇓-WhileNil ≡VNil) rewrite ≡VNil =
  ⇓-WhileNil ≡VNil
⊨While-unrollToInit⇒ hs (⇓-WhileBottom ≡VBottom) rewrite ≡VBottom =
  ⇓-WhileBottom hs
⊨While-unrollToInit⇒ hs (⇓-WhileCons ≡VCons h) rewrite ≡VCons =
  h

⊨While-unrollToInit⇐ :
  ∀  {cond e v v′} →
    strictTrm cond →
    [ cond ] e ⊨While evalT (IfNil cond Id e) v ⇓  v′ →
    [ cond ] e ⊨While v ⇓ v′

⊨While-unrollToInit⇐ {cond} {e} {v} {v′} hs hw
  with evalT cond v | inspect (evalT cond) v

⊨While-unrollToInit⇐ hs hw
  | VNil | [ g ]ⁱ = hw

⊨While-unrollToInit⇐ hs hw
  | VCons v1 v2 | [ g ]ⁱ = ⇓-WhileCons g hw

⊨While-unrollToInit⇐ hs (⇓-WhileNil ≡VNil)
  | VBottom | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unrollToInit⇐ hs (⇓-WhileBottom ≡VBottom)
  | VBottom | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unrollToInit⇐ hs (⇓-WhileCons ≡VCons h)
  | VBottom | [ g ]ⁱ =
  ⊥-elim (VCons≢VBottom (trans (P.sym ≡VCons) hs))

-- ⊨While-unrollToInit

⊨While-unrollToInit :
  ∀ {cond e v v′} →
    strictTrm cond →
    [ cond ] e ⊨While v ⇓ v′ ⇔
    [ cond ] e ⊨While evalT (IfNil cond Id e) v ⇓  v′

⊨While-unrollToInit hs =
  equivalence (⊨While-unrollToInit⇒ hs) (⊨While-unrollToInit⇐ hs)

-- ⊨KNF-unrollToInit⇒-lemma

⊨KNF-unrollToInit⇒-lemma :
  ∀ init cond body v →
      evalNT (propagateIfCond
        (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
                  (normConv init))) v
      ≡
      ifNil (evalT cond (evalT init v))
            (evalT init v) (evalT body (evalT init v))

⊨KNF-unrollToInit⇒-lemma init cond body v = begin
  evalNT (propagateIfCond
    (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
              (normConv init))) v
    ≡⟨ evalNT∘propagateIfCond 
       (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
                 (normConv init)) v ⟩
  evalNT (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
                   (normConv init)) v
    ≡⟨ evalNT∘normNCmp
       (normNIf (normConv cond) (NSelCmp []) (normConv body))
                (normConv init) v ⟩
  evalNT (normNIf (normConv cond) (NSelCmp []) (normConv body))
         (evalNT (normConv init) v)
    ≡⟨ cong (evalNT (normNIf (normConv cond) (NSelCmp []) (normConv body)))
            (evalNT∘normConv init v) ⟩
  evalNT (normNIf (normConv cond) (NSelCmp []) (normConv body)) (evalT init v)
    ≡⟨ evalNT∘normNIf
       (normConv cond) (NSelCmp []) (normConv body) (evalT init v) ⟩
  ifNil (evalNT (normConv cond) (evalT init v))
        (evalNT (NSelCmp []) (evalT init v))
        (evalNT (normConv body) (evalT init v))
    ≡⟨ ifNil-cong (evalNT∘normConv cond (evalT init v)) refl
                  (evalNT∘normConv body (evalT init v)) ⟩
  ifNil (evalT cond (evalT init v)) (evalT init v) (evalT body (evalT init v))
  ∎
  where open ≡-Reasoning

-- ⊨KNF-unrollToInit⇒

⊨KNF-unrollToInit⇒ :
  ∀ {knf v v′} →
    strictTrm (condExp knf) →
    knf ⊨KNF v ⇓ v′ → unrollToInit knf ⊨KNF v ⇓ v′

⊨KNF-unrollToInit⇒ hs (⇓-eval {init} {cond} {body} {final} {v} {v′} hw)
  rewrite evalNT∘propagateIfCond
    ((normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
               (normConv init))) v
  = ⇓-eval (helper hw)
  where
  open Related.EquationalReasoning
  helper =
    [ cond ] body ⊨While evalT init v ⇓ v′
      ∼⟨ ⊨While-unrollToInit⇒ hs ⟩
    [ cond ] body ⊨While
      ifNil (evalT cond (evalT init v))
            (evalT init v) (evalT body (evalT init v)) ⇓ v′
      ∼⟨ subst (flip ([_]_⊨While_⇓_ cond body) v′)
               (P.sym $ ⊨KNF-unrollToInit⇒-lemma init cond body v) ⟩
    [ cond ] body ⊨While
      evalNT (propagateIfCond (normNCmp (normNIf (normConv cond) (NSelCmp [])
                                                 (normConv body))
                                        (normConv init))) v ⇓ v′
    ∎

-- ⊨KNF-unrollToInit⇐

⊨KNF-unrollToInit⇐ :
  ∀ {knf v v′} →
    strictTrm (condExp knf) →
    unrollToInit knf ⊨KNF v ⇓ v′ → knf ⊨KNF v ⇓ v′

⊨KNF-unrollToInit⇐ hs = {!!}

-- ⊨KNF-unrollToInit

⊨KNF-unrollToInit :
  ∀ {knf v v′} →
    strictTrm (condExp knf) →
    knf ⊨KNF v ⇓ v′ ⇔ unrollToInit knf ⊨KNF v ⇓ v′

⊨KNF-unrollToInit hs =
  equivalence (⊨KNF-unrollToInit⇒ hs) (⊨KNF-unrollToInit⇐ hs)

-- evalKNF-unrollToInit

evalKNF-unrollToInit :
  ∀ knf v v′ → strictTrm (condExp knf) →
    (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
    (∃ λ (i′ : ℕ) → evalKNF i′ (unrollToInit knf) v ≡ just v′)

evalKNF-unrollToInit knf v v′ hs =
  (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′)
    ∼⟨ sym $ ⊨KNF⇔evalKNF ⟩
  knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF-unrollToInit hs ⟩
  unrollToInit knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF⇔evalKNF ⟩
  (∃ λ (i′ : ℕ) → evalKNF i′ (unrollToInit knf) v ≡ just v′)
  ∎
  where open Related.EquationalReasoning

--
