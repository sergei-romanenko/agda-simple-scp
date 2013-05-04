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
  hiding (sym)
  renaming ([_] to [_]ⁱ)

import Function.Related as Related

open import Util
open import ExpLang
open import PositiveInfo
open import ImpLang

------------------
-- ⊨KNF-unrollers
------------------

-- In this module, the main result will be that
--   ⊨KNF-unroller norm∘KNF-unroll .

-- ⊨KNF-unroller

⊨KNF-unroller : (KNFProg → KNFProg) → Set

⊨KNF-unroller unroll =
  ∀ {knf v v′} →
    StrictKNF knf →
    (knf ⊨KNF v ⇓ v′) ⇔ (unroll knf ⊨KNF v ⇓ v′)

-- norm∘KNF-unroll

norm∘KNF-unroll : KNFProg → KNFProg

norm∘KNF-unroll (KNF init cond body final) =
  KNF newInit cond body final
  where newInit = ⌈ norm $ (IfNil cond Id body) $$ init ⌉

--------------------
-- ⊨While-unrollers
--------------------

⊨While-unroller : (Trm → Trm → Trm) → Set

⊨While-unroller unroll =
  ∀  {cond body v v′} →
    StrictTrm cond →
    [ cond ] body ⊨While v ⇓ v′ ⇔
    [ cond ] body ⊨While ⟦ unroll cond body ⟧ v ⇓  v′

-- while-unroll

while-unroll : Trm → Trm → Trm

while-unroll cond body = IfNil cond Id body


--------------------------------
-- ⊨While-unroller while-unroll
--------------------------------

-- ⊨While-unroll⇒

⊨While-unroll⇒ :
  ∀  {cond body v v′} →
    StrictTrm cond →
    [ cond ] body ⊨While v ⇓ v′ →
    [ cond ] body ⊨While ⟦ while-unroll cond body ⟧ v ⇓  v′

⊨While-unroll⇒ hs (⇓-WhileNil ≡[]ˣ) rewrite ≡[]ˣ =
  ⇓-WhileNil ≡[]ˣ
⊨While-unroll⇒ hs (⇓-WhileBottom ≡↯ˣ) rewrite ≡↯ˣ =
  ⇓-WhileBottom hs
⊨While-unroll⇒ hs (⇓-WhileCons ≡∷ˣ h) rewrite ≡∷ˣ =
  h

-- ⊨While-unroll⇐

⊨While-unroll⇐ :
  ∀  {cond body v v′} →
    StrictTrm cond →
    [ cond ] body ⊨While ⟦ while-unroll cond body ⟧ v ⇓  v′ →
    [ cond ] body ⊨While v ⇓ v′

⊨While-unroll⇐ {cond} {body} {v} {v′} hs hw
  with ⟦ cond ⟧ v | inspect ⟦ cond ⟧ v

⊨While-unroll⇐ hs hw
  | []ˣ | [ g ]ⁱ = hw

⊨While-unroll⇐ hs hw
  | v1 ∷ˣ v2 | [ g ]ⁱ = ⇓-WhileCons g hw

⊨While-unroll⇐ hs (⇓-WhileNil ≡[]ˣ)
  | ↯ˣ | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unroll⇐ hs (⇓-WhileBottom ≡↯ˣ)
  | ↯ˣ | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unroll⇐ hs (⇓-WhileCons ≡∷ˣ h)
  | ↯ˣ | [ g ]ⁱ =
  ⊥-elim (∷ˣ≢↯ˣ (trans (P.sym ≡∷ˣ) hs))

-- ⊨While-unroll

⊨While-unroll : ⊨While-unroller while-unroll

⊨While-unroll hs =
  equivalence (⊨While-unroll⇒ hs) (⊨While-unroll⇐ hs)

--------------------------------------
-- ⊨KNF-unroller norm∘KNF-unroll
--------------------------------------

-- propagateIfCond∘○

propagateIfCond∘○ :
  ∀ (init body : Trm) →
    ⟦⌈ propagateIfCond (⌋ body ⌊ ○ ⌋ init ⌊) ⌉⟧ ≗ ⟦ body ⟧ ∘ ⟦ init ⟧

propagateIfCond∘○ init body v =
  begin
    ⟦⌈ propagateIfCond (⌋ body ⌊ ○ ⌋ init ⌊) ⌉⟧ v
      ≡⟨ ⟦⌈⌉⟧∘propagateIfCond (⌋ body ⌊ ○ ⌋ init ⌊) v ⟩
    ⟦⌈ ⌋ body ⌊ ○ ⌋ init ⌊ ⌉⟧ v
      ≡⟨ ⟦⌈⌉⟧∘○ ⌋ body ⌊ ⌋ init ⌊ v ⟩
    ⟦⌈ ⌋ body ⌊ ⌉⟧ (⟦⌈ ⌋ init ⌊ ⌉⟧ v)
      ≡⟨ ⟦⌈⌉⟧∘⌋⌊ body (⟦ ⌈ ⌋ init ⌊ ⌉ ⟧ v) ⟩
    ⟦ body ⟧ (⟦⌈ ⌋ init ⌊ ⌉⟧ v)
      ≡⟨ cong ⟦ body ⟧ (⟦⌈⌉⟧∘⌋⌊ init v) ⟩
    ⟦ body ⟧ (⟦ init ⟧ v)
  ∎
  where open ≡-Reasoning

-- ⊨While-propagateIfCond

⊨While-propagateIfCond :
  ∀ (init cond body : Trm) (v v′ : Val) →
    StrictTrm cond →
    [ cond ] body ⊨While ⟦ init ⟧ v ⇓ v′ ⇔
    [ cond ] body ⊨While
      ⟦⌈ propagateIfCond (⌋ while-unroll cond body ⌊ ○ ⌋ init ⌊) ⌉⟧ v ⇓ v′

⊨While-propagateIfCond init cond body v v′ hs =
  [ cond ] body ⊨While ⟦ init ⟧ v ⇓ v′
    ∼⟨ ⊨While-unroll hs ⟩
  [ cond ] body ⊨While ⟦ while-unroll cond body ⟧ (⟦ init ⟧ v) ⇓ v′
    ≡⟨ cong (flip ([_]_⊨While_⇓_ cond body) v′)
         (P.sym $ propagateIfCond∘○ init (while-unroll cond body) v) ⟩
  [ cond ] body ⊨While
    ⟦⌈ propagateIfCond (⌋ while-unroll cond body ⌊ ○ ⌋ init ⌊) ⌉⟧ v ⇓ v′
  ∎
  where open Related.EquationalReasoning

-- ⊨norm∘KNF-unroll-correct⇒

⊨norm∘KNF-unroll-correct⇒ :
  ∀ {knf v v′} → StrictKNF knf →
    knf ⊨KNF v ⇓ v′ → norm∘KNF-unroll knf ⊨KNF v ⇓ v′

⊨norm∘KNF-unroll-correct⇒
  {KNF init cond body final} {v} hs (⇓-eval {v′ = v′} hw)
  = ⇓-eval (Equivalence.to
             (⊨While-propagateIfCond init cond body v v′ hs) ⟨$⟩ hw)

-- ⊨norm∘KNF-unroll-correct⇐

⊨norm∘KNF-unroll-correct⇐ :
  ∀ {knf v v′} → StrictKNF knf →
    norm∘KNF-unroll knf ⊨KNF v ⇓ v′ → knf ⊨KNF v ⇓ v′

⊨norm∘KNF-unroll-correct⇐
  {KNF init cond body final} {v} hs (⇓-eval {v′ = v′} hw)
  = ⇓-eval (Equivalence.from
             (⊨While-propagateIfCond init cond body v v′ hs) ⟨$⟩ hw)

-- ⊨KNF-unroller-with-norm

⊨KNF-unroller-with-norm : ⊨KNF-unroller norm∘KNF-unroll

⊨KNF-unroller-with-norm hs = 
  equivalence (⊨norm∘KNF-unroll-correct⇒ hs) (⊨norm∘KNF-unroll-correct⇐ hs)

--
