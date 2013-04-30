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
    [ cond ] e ⊨While ⟦ IfNil cond Id e ⟧ v ⇓  v′

⊨While-unrollToInit⇒ hs (⇓-WhileNil ≡[]ˣ) rewrite ≡[]ˣ =
  ⇓-WhileNil ≡[]ˣ
⊨While-unrollToInit⇒ hs (⇓-WhileBottom ≡↯ˣ) rewrite ≡↯ˣ =
  ⇓-WhileBottom hs
⊨While-unrollToInit⇒ hs (⇓-WhileCons ≡∷ˣ h) rewrite ≡∷ˣ =
  h

-- ⊨While-unrollToInit⇐

⊨While-unrollToInit⇐ :
  ∀  {cond e v v′} →
    StrictTrm cond →
    [ cond ] e ⊨While ⟦ IfNil cond Id e ⟧ v ⇓  v′ →
    [ cond ] e ⊨While v ⇓ v′

⊨While-unrollToInit⇐ {cond} {e} {v} {v′} hs hw
  with ⟦ cond ⟧ v | inspect ⟦ cond ⟧ v

⊨While-unrollToInit⇐ hs hw
  | []ˣ | [ g ]ⁱ = hw

⊨While-unrollToInit⇐ hs hw
  | v1 ∷ˣ v2 | [ g ]ⁱ = ⇓-WhileCons g hw

⊨While-unrollToInit⇐ hs (⇓-WhileNil ≡[]ˣ)
  | ↯ˣ | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unrollToInit⇐ hs (⇓-WhileBottom ≡↯ˣ)
  | ↯ˣ | [ g ]ⁱ = ⇓-WhileBottom g

⊨While-unrollToInit⇐ hs (⇓-WhileCons ≡∷ˣ h)
  | ↯ˣ | [ g ]ⁱ =
  ⊥-elim (∷ˣ≢↯ˣ (trans (P.sym ≡∷ˣ) hs))

-- ⊨While-unrollToInit

⊨While-unrollToInit :
  ∀ {cond e v v′} →
    StrictTrm cond →
    [ cond ] e ⊨While v ⇓ v′ ⇔
    [ cond ] e ⊨While ⟦ IfNil cond Id e ⟧ v ⇓  v′

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
      ⟦⌈ propagateIfCond
         (IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ○ ⌋ init ⌊) ⌉⟧ v
      ≡
      ifNil (⟦ cond ⟧ (⟦ init ⟧ v))
            (⟦ init ⟧ v) (⟦ body ⟧ (⟦ init ⟧ v))

⊨KNF-unrollToInit-lemma₁ init cond body v = begin
  ⟦⌈ propagateIfCond
     (IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ○ ⌋ init ⌊) ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘propagateIfCond
       (IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ○ ⌋ init ⌊) v ⟩
  ⟦⌈ IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ○ ⌋ init ⌊ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○ (IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊) ⌋ init ⌊ v ⟩
  ⟦⌈ IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ⌉⟧
             (⟦⌈ ⌋ init ⌊ ⌉⟧ v)
    ≡⟨ cong ⟦⌈ IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ⌉⟧
            (⟦⌈⌉⟧∘⌋⌊ init v) ⟩
  ⟦⌈ IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ⌉⟧ (⟦ init ⟧ v)
    ≡⟨ ⟦⌈⌉⟧∘IfNilⁿ⟱
       (⌋ cond ⌊) ⟪ [] ⟫ⁿ (⌋ body ⌊) (⟦ init ⟧ v) ⟩
  ifNil (⟦⌈ ⌋ cond ⌊ ⌉⟧ (⟦ init ⟧ v))
        (⟦⌈ ⟪ [] ⟫ⁿ ⌉⟧ (⟦ init ⟧ v))
        (⟦⌈ ⌋ body ⌊ ⌉⟧ (⟦ init ⟧ v))
    ≡⟨ ifNil-cong (⟦⌈⌉⟧∘⌋⌊ cond (⟦ init ⟧ v)) refl
                  (⟦⌈⌉⟧∘⌋⌊ body (⟦ init ⟧ v)) ⟩
  ifNil (⟦ cond ⟧ (⟦ init ⟧ v)) (⟦ init ⟧ v) (⟦ body ⟧ (⟦ init ⟧ v))
  ∎
  where open ≡-Reasoning

-- ⊨KNF-unrollToInit-lemma₂

⊨KNF-unrollToInit-lemma₂ :
  ∀ (init cond body final : Trm) (v v′ : Val) →
    StrictTrm cond →
    [ cond ] body ⊨While ⟦ init ⟧ v ⇓ v′ ⇔
    [ cond ] body ⊨While
      ⟦⌈ propagateIfCond
           (IfNilⁿ⟱ ⌋ cond ⌊ ⟪ [] ⟫ⁿ ⌋ body ⌊ ○ ⌋ init ⌊) ⌉⟧ v ⇓ v′

⊨KNF-unrollToInit-lemma₂ init cond body final v v′ hs =
  [ cond ] body ⊨While ⟦ init ⟧ v ⇓ v′
    ∼⟨ ⊨While-unrollToInit hs ⟩
  [ cond ] body ⊨While
    ifNil (⟦ cond ⟧ (⟦ init ⟧ v))
          (⟦ init ⟧ v) (⟦ body ⟧ (⟦ init ⟧ v)) ⇓ v′
    ≡⟨ ⊨While-cong-v (P.sym $ ⊨KNF-unrollToInit-lemma₁ init cond body v) ⟩
  [ cond ] body ⊨While
    ⟦⌈ propagateIfCond (IfNilⁿ⟱ (⌋ cond ⌊) ⟪ [] ⟫ⁿ (⌋ body ⌊) ○
                       ⌋ init ⌊) ⌉⟧ v ⇓ v′
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
