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
open import Function.Equality
  using (_⟨$⟩_; module Π)
open import Function.Equivalence
  using (module Equivalence; _⇔_; equivalence)


open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; trans; cong; subst; inspect; module ≡-Reasoning)
  renaming ([_] to [_]ⁱ)

import Function.Related as Related

open import Util
open import ExpLang
open import PositiveInfo
open import ImpLang

--
-- ⊨KNF-unroller
--

-- TODO: `unrollToInit` might be abstracted away from some theorems...

⊨KNF-unroller : (KNFProg → KNFProg) → Set

⊨KNF-unroller unroll =
  ∀ {knf v v′} →
    StrictKNF knf →
    (knf ⊨KNF v ⇓ v′) ⇔ (unroll knf ⊨KNF v ⇓ v′)

-- unrollToInit

unrollToInit : KNFProg → KNFProg

unrollToInit (KNF initExp condExp bodyExp finalExp) =
  KNF newInit condExp bodyExp finalExp
  where newInit = ⌈ norm $ (IfNil condExp Id bodyExp) $$ initExp ⌉

-----------------------------------
-- Unrolling respects the semantics
-----------------------------------

-- ⊨While-unrollToInit⇒

⊨While-unrollToInit⇒ :
  ∀  {cond e v v′} →
    StrictTrm cond →
    [ cond ] e ⊨While v ⇓ v′ →
    [ cond ] e ⊨While ⟦_⟧ (IfNil cond Id e) v ⇓  v′

⊨While-unrollToInit⇒ hs (⇓-WhileNil ≡VNil) rewrite ≡VNil =
  ⇓-WhileNil ≡VNil
⊨While-unrollToInit⇒ hs (⇓-WhileBottom ≡VBottom) rewrite ≡VBottom =
  ⇓-WhileBottom hs
⊨While-unrollToInit⇒ hs (⇓-WhileCons ≡VCons h) rewrite ≡VCons =
  h

-- ⊨While-unrollToInit⇐

⊨While-unrollToInit⇐ :
  ∀  {cond e v v′} →
    StrictTrm cond →
    [ cond ] e ⊨While ⟦_⟧ (IfNil cond Id e) v ⇓  v′ →
    [ cond ] e ⊨While v ⇓ v′

⊨While-unrollToInit⇐ {cond} {e} {v} {v′} hs hw
  with ⟦_⟧ cond v | inspect (⟦_⟧ cond) v

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
    StrictTrm cond →
    [ cond ] e ⊨While v ⇓ v′ ⇔
    [ cond ] e ⊨While ⟦_⟧ (IfNil cond Id e) v ⇓  v′

⊨While-unrollToInit hs =
  equivalence (⊨While-unrollToInit⇒ hs) (⊨While-unrollToInit⇐ hs)

-- ⊨While-cong-v

⊨While-cong-v :
  ∀ {cond body v₁ v₂ v′} →
    v₁ ≡ v₂ →
    [ cond ] body ⊨While v₁ ⇓ v′ ≡ [ cond ] body ⊨While v₂ ⇓ v′

⊨While-cong-v {cond} {body} {v₁} {v₂} {v′} v₁≡v₂ =
  cong (flip ([_]_⊨While_⇓_ cond body) v′) v₁≡v₂

-- ⊨KNF-unrollToInit⇒-lemma₁

⊨KNF-unrollToInit-lemma₁ :
  ∀ init cond body v →
      ⟦⌈_⌉⟧ (propagateIfCond
        (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
                  (normConv init))) v
      ≡
      ifNil (⟦_⟧ cond (⟦_⟧ init v))
            (⟦_⟧ init v) (⟦_⟧ body (⟦_⟧ init v))

⊨KNF-unrollToInit-lemma₁ init cond body v = begin
  ⟦⌈_⌉⟧ (propagateIfCond
    (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
              (normConv init))) v
    ≡⟨ ⟦⌈⌉⟧∘propagateIfCond
       (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
                 (normConv init)) v ⟩
  ⟦⌈_⌉⟧ (normNCmp (normNIf (normConv cond) (NSelCmp []) (normConv body))
                   (normConv init)) v
    ≡⟨ ⟦⌈⌉⟧∘normNCmp
       (normNIf (normConv cond) (NSelCmp []) (normConv body))
                (normConv init) v ⟩
  ⟦⌈_⌉⟧ (normNIf (normConv cond) (NSelCmp []) (normConv body))
         (⟦⌈_⌉⟧ (normConv init) v)
    ≡⟨ cong (⟦⌈_⌉⟧ (normNIf (normConv cond) (NSelCmp []) (normConv body)))
            (⟦⌈⌉⟧∘normConv init v) ⟩
  ⟦⌈_⌉⟧ (normNIf (normConv cond) (NSelCmp []) (normConv body)) (⟦_⟧ init v)
    ≡⟨ ⟦⌈⌉⟧∘normNIf
       (normConv cond) (NSelCmp []) (normConv body) (⟦_⟧ init v) ⟩
  ifNil (⟦⌈_⌉⟧ (normConv cond) (⟦_⟧ init v))
        (⟦⌈_⌉⟧ (NSelCmp []) (⟦_⟧ init v))
        (⟦⌈_⌉⟧ (normConv body) (⟦_⟧ init v))
    ≡⟨ ifNil-cong (⟦⌈⌉⟧∘normConv cond (⟦_⟧ init v)) refl
                  (⟦⌈⌉⟧∘normConv body (⟦_⟧ init v)) ⟩
  ifNil (⟦_⟧ cond (⟦_⟧ init v)) (⟦_⟧ init v) (⟦_⟧ body (⟦_⟧ init v))
  ∎
  where open ≡-Reasoning

-- ⊨KNF-unrollToInit-lemma₂

⊨KNF-unrollToInit-lemma₂ :
  ∀ (init cond body final : Trm) (v v′ : Val) →
    StrictTrm cond →
    [ cond ] body ⊨While ⟦_⟧ init v ⇓ v′ ⇔
    [ cond ] body ⊨While
      ⟦⌈_⌉⟧ (propagateIfCond (normNCmp (normNIf (normConv cond) (NSelCmp [])
                                                 (normConv body))
                                        (normConv init))) v ⇓ v′

⊨KNF-unrollToInit-lemma₂ init cond body final v v′ hs =
  [ cond ] body ⊨While ⟦_⟧ init v ⇓ v′
    ∼⟨ ⊨While-unrollToInit hs ⟩
  [ cond ] body ⊨While
    ifNil (⟦_⟧ cond (⟦_⟧ init v))
          (⟦_⟧ init v) (⟦_⟧ body (⟦_⟧ init v)) ⇓ v′
    ≡⟨ ⊨While-cong-v (P.sym $ ⊨KNF-unrollToInit-lemma₁ init cond body v) ⟩
  [ cond ] body ⊨While
    ⟦⌈_⌉⟧ (propagateIfCond (normNCmp (normNIf (normConv cond) (NSelCmp [])
                                               (normConv body))
                                      (normConv init))) v ⇓ v′
  ∎
  where open Related.EquationalReasoning

-- ⊨KNF-unrollToInit⇒

⊨KNF-unrollToInit⇒ :
  ∀ {knf v v′} →
    StrictKNF knf →
    knf ⊨KNF v ⇓ v′ → unrollToInit knf ⊨KNF v ⇓ v′

⊨KNF-unrollToInit⇒ hs (⇓-eval {init} {cond} {body} {final} {v} {v′} hw) =
  ⇓-eval (Equivalence.to
           (⊨KNF-unrollToInit-lemma₂ init cond body final v v′ hs) ⟨$⟩ hw)

-- ⊨KNF-unrollToInit⇐

⊨KNF-unrollToInit⇐ :
  ∀ {knf v v′} →
    StrictKNF knf →
    unrollToInit knf ⊨KNF v ⇓ v′ → knf ⊨KNF v ⇓ v′

⊨KNF-unrollToInit⇐ {KNF init cond body final} {v} hs (⇓-eval {v′ = v′} hw) =
  ⇓-eval (Equivalence.from
           (⊨KNF-unrollToInit-lemma₂ init cond body final v v′ hs) ⟨$⟩ hw)

-- unrollToInit-is-⊨KNF-unroller

unrollToInit-is-⊨KNF-unroller : ⊨KNF-unroller unrollToInit
unrollToInit-is-⊨KNF-unroller hs = 
  equivalence (⊨KNF-unrollToInit⇒ hs) (⊨KNF-unrollToInit⇐ hs)

--
