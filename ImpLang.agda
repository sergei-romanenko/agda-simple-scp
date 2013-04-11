--
-- A Turing-complete Imperative Language
--

module ImpLang where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product

open import Function
open import Function.Equivalence
  using (_⇔_; equivalence)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

import Function.Related as Related

open import Data.Nat.Properties
  --using (⊔-⊓-0-isCommutativeSemiringWithoutOne; m≤m⊔n; n∸m≤n)

open import Algebra.Structures
  using (module IsCommutativeSemiringWithoutOne)

open import Util
open import ExpLang
open import PosInfoProp

-- We embed the language of simple expressions inside a small
-- imperative language with assignments and while-loops (called here SWhile).

data Stmt : Set where
  Assign : (t : Trm) → Stmt
  Seq    : (s1 s2 : Stmt) → Stmt
  While  : (t : Trm) → (s : Stmt) → Stmt

-- Since this language is Turing-complete, we cannot specify
-- its evaluator as a total Agda function.
-- Thus we specify its semantics as a relation.

data SWhileEvalRel : Val → Stmt → Val → Set where
  SWhileEvalAssign :
    ∀ {t v} → SWhileEvalRel v (Assign t) (evalT t v) 
  SWhileEvalSeq :
    ∀ {s1 s2 v v′ v′′} →
    SWhileEvalRel v s1 v′ → SWhileEvalRel v′ s2 v′′ →
    SWhileEvalRel v (Seq s1 s2) v′′
  SWhileEvalWhileNil :
    ∀ {cond s v} →
    evalT cond v ≡ VNil →
    SWhileEvalRel v (While cond s) v
  SWhileEvalWhileBottom :
    ∀ {cond s v} →
    evalT cond v ≡ VBottom →
    SWhileEvalRel v (While cond s) VBottom
  SWhileEvalWhileCons :
    ∀ {cond s v v′ v′′ vh vt} →
    evalT cond v ≡ VCons vh vt →
    SWhileEvalRel v s v′ → SWhileEvalRel v′ (While cond s) v′′ →
    SWhileEvalRel v (While cond s) v′′

-- A `KNF` program contains a single while loop.
-- This is an analog of Kleene's normal form (KNF) from recursion theory.
-- An analog of the "Kleene normal form" for SWhile programs
-- can be represented as a record of 4 simple expressions

record KNFProg : Set where
  constructor NFProg
  field
    initExp  : Trm
    condExp  : Trm
    bodyExp  : Trm
    finalExp : Trm

open KNFProg public

KNFtoProg : KNFProg → Stmt
KNFtoProg knf =
  Seq (Assign (initExp knf))
      (Seq (While (condExp knf) (Assign (bodyExp knf)))
           (Assign (finalExp knf)))

-- Many optimizing transformations are valid
-- only if the condition of the loop is strict,
-- according to the following definition.

-- strictTrm

strictTrm : Trm → Set
strictTrm t = evalT t VBottom ≡ VBottom

-- The strictness of terms in normal form is decidable.

-- strictNTrm

strictNTrm : NTrm → Set
strictNTrm nt = evalNT nt VBottom ≡ VBottom

-- strictNTrm?

strictNTrm? : (nt : NTrm) → Dec (strictNTrm nt)

strictNTrm? NNil = no (λ ())

strictNTrm? (NCons nt1 nt2) = no (λ ())

strictNTrm? (NSelCmp sels) = yes $ begin
  evalNT (NSelCmp sels) VBottom
    ≡⟨ refl ⟩
  evalT (sels2trm sels) VBottom
    ≡⟨ evalT∘sels2trm sels VBottom ⟩
  evalSels VBottom sels
    ≡⟨ evalSels-VBottom sels ⟩
  VBottom
  ∎
  where open ≡-Reasoning

strictNTrm? (NIfNil sels nt1 nt2) = yes $ begin
  ifNil (evalT (sels2trm sels) VBottom)
        (evalNT nt1 VBottom) (evalNT nt2 VBottom)
    ≡⟨ ifNil-cong (evalT∘sels2trm sels VBottom) refl refl ⟩
  ifNil (evalSels VBottom sels)
        (evalNT nt1 VBottom) (evalNT nt2 VBottom)
    ≡⟨ ifNil-cong (evalSels-VBottom sels) refl refl ⟩
  VBottom
  ∎
  where open ≡-Reasoning

strictNTrm? NBottom = yes refl

-- The strictness of terms in normal form is decidable.
-- We just normalize the term and then apply `strictNTrm?`.

-- strictTrm?

strictTrm? : (t : Trm) → Dec (strictTrm t)
strictTrm? t
  rewrite sym $ evalNT∘normConv t VBottom
  = strictNTrm? (normConv t)

----------------------------------------------------------
-- Evaluation semantics for SWhile programs.
-- We add an extra parameter limiting the recursion depth,
-- in order to make functions total.
----------------------------------------------------------

-- _>>=_

_>>=_ : (v? : Maybe Val) → (f : Val → Maybe Val) → Maybe Val
just v  >>= f = f v
nothing >>= f = nothing

-- evalS

evalS : (d : ℕ) (s : Stmt) (v : Val) → Maybe Val
evalS-While :
  (d : ℕ) (t : Trm) (s : Stmt) (v : Val) (r : Val) → Maybe Val

evalS zero s v = nothing
evalS (suc d) (Assign t) v = just (evalT t v)
evalS (suc d) (Seq s1 s2) v =
  evalS d s1 v >>= evalS d s2
evalS (suc d) (While t s) v =
  evalS-While d t s v (evalT t v)

evalS-While d t s v VNil =
  just v

evalS-While d t s v (VCons v1 v2) =
  evalS d s v >>= evalS d (While t s)

evalS-While d t s v VBottom = just VBottom

-----------------------------------------------------
-- The executable interpreter is correct with respect
-- to the relational semantics.
-----------------------------------------------------

-- Auxiliaries

<′⇨≤′ : {i j : ℕ} → i <′ j → i ≤′ j
<′⇨≤′ ≤′-refl = ≤′-step ≤′-refl
<′⇨≤′ (≤′-step m≤′n) = ≤′-step (<′⇨≤′ m≤′n)

n≤m⊔n : ∀ m n → n ≤ m ⊔ n
n≤m⊔n m n = subst (_≤_ n) (+-comm _ m) (m≤m⊔n _ _)
  where
  open IsCommutativeSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne

-- evalS-mono

evalS-mono : (s : Stmt) (i j : ℕ) → i ≤′ j → (v v′ : Val) →
    evalS i s v ≡ just v′ → evalS j s v ≡ just v′

evalS-mono s zero j i≤′j v v′ ()

evalS-mono s (suc i) zero () v v′ h

evalS-mono s (suc .j) (suc j) ≤′-refl v v′ h = h

evalS-mono s (suc i) (suc j) (≤′-step m≤′n) v v′′ h = helper s h
  where
  helper : (s : Stmt) →
    evalS (suc i) s v ≡ just v′′ → evalS (suc j) s v ≡ just v′′

  helper (Assign t) h′ = h′

  helper (Seq s1 s2) h′ with evalS i s1 v | inspect (evalS i s1) v
  helper (Seq s1 s2) h′ | just v′ | [ g₁ ]ⁱ
    rewrite evalS-mono s1 i j (<′⇨≤′ m≤′n) v v′ g₁
    = evalS-mono s2 i j (<′⇨≤′ m≤′n) v′ v′′ h′
  helper (Seq s1 s2) () | nothing | [ g₁ ]ⁱ

  helper (While t s') h′ with evalT t v
  helper (While t s') h′ | VNil = h′
  helper (While t s') h′ | VCons v1 v2
    with evalS i s' v | inspect (evalS i s') v
  ... | just v′ | [ g ]ⁱ
    rewrite evalS-mono s' i j (<′⇨≤′ m≤′n) v v′ g
    = evalS-mono (While t s') i j (<′⇨≤′ m≤′n) v′ v′′ h′
  helper (While t s') () | VCons v1 v2 | nothing | [ g ]ⁱ
  helper (While t s') h′ | VBottom = h′

-- evalS⇒SWhileEvalRel

evalS⇒SWhileEvalRel :
  ∀ s v v′ →
    SWhileEvalRel v s v′ →
    (∃ λ (i : ℕ) → evalS i s v ≡ just v′)

evalS⇒SWhileEvalRel (Assign t) v .(evalT t v) SWhileEvalAssign =
  suc zero , refl

evalS⇒SWhileEvalRel (Seq s1 s2) v v′′ (SWhileEvalSeq {v′ = v′} h₁ h₂)
  with evalS⇒SWhileEvalRel s1 v v′ h₁ | evalS⇒SWhileEvalRel s2 v′ v′′ h₂
... | i₁ , g₁ | i₂ , g₂ = suc (i₁ ⊔ i₂) , (begin
    evalS (i₁ ⊔ i₂) s1 v >>= evalS (i₁ ⊔ i₂) s2
      ≡⟨ cong (flip _>>=_ (evalS (i₁ ⊔ i₂) s2))
              (evalS-mono s1 i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) v v′ g₁) ⟩
    evalS (i₁ ⊔ i₂) s2 v′
      ≡⟨ evalS-mono s2 i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) v′ v′′ g₂ ⟩
    just v′′
    ∎)
  where open ≡-Reasoning

evalS⇒SWhileEvalRel (While t s) .v′′ v′′ (SWhileEvalWhileNil ≡VNil) =
  suc zero , (begin
    evalS-While zero t s v′′ (evalT t v′′)
      ≡⟨ cong (evalS-While zero t s v′′) ≡VNil ⟩
    just v′′
    ∎)
  where open ≡-Reasoning

evalS⇒SWhileEvalRel (While t s) v .VBottom (SWhileEvalWhileBottom ≡VBottom) =
  suc zero , (begin
    evalS-While zero t s v (evalT t v)
      ≡⟨ cong (evalS-While zero t s v) ≡VBottom ⟩
    just VBottom
    ∎)
  where open ≡-Reasoning

evalS⇒SWhileEvalRel (While t s) v v′′
  (SWhileEvalWhileCons {v′ = v′} ≡VCons h₁ h₂)
  with evalS⇒SWhileEvalRel s v v′ h₁ | evalS⇒SWhileEvalRel (While t s) v′ v′′ h₂
... | i₁ , g₁ | i₂ , g₂ = suc (i₁ ⊔ i₂) , (begin
    evalS-While (i₁ ⊔ i₂) t s v (evalT t v)
      ≡⟨ cong (evalS-While (i₁ ⊔ i₂) t s v) ≡VCons ⟩
    evalS (i₁ ⊔ i₂) s v >>= evalS (i₁ ⊔ i₂) (While t s)
      ≡⟨ cong (flip _>>=_ (evalS (i₁ ⊔ i₂) (While t s)))
              (evalS-mono s i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) v v′ g₁) ⟩
    evalS (i₁ ⊔ i₂) (While t s) v′
      ≡⟨ evalS-mono (While t s) i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) v′ v′′ g₂ ⟩
    just v′′
    ∎)
  where open ≡-Reasoning

-- evalS⇐SWhileEvalRel

evalS⇐SWhileEvalRel :
  ∀ i s v v′ →
    evalS i s v ≡ just v′ →
    SWhileEvalRel v s v′

evalS⇐SWhileEvalRel zero s v v′′ ()

evalS⇐SWhileEvalRel (suc i) (Assign t) v .(evalT t v) refl =
  SWhileEvalAssign

evalS⇐SWhileEvalRel (suc i) (Seq s1 s2) v v′′ h
  with evalS i s1 v | inspect (evalS i s1) v

evalS⇐SWhileEvalRel (suc i) (Seq s1 s2) v v′′ h
  | just v′ | [ g₁ ]ⁱ
  = SWhileEvalSeq (evalS⇐SWhileEvalRel i s1 v v′ g₁)
                  (evalS⇐SWhileEvalRel i s2 v′ v′′ h)

evalS⇐SWhileEvalRel (suc i) (Seq s1 s2) v v′′ ()
  | nothing | [ g₁ ]ⁱ

evalS⇐SWhileEvalRel (suc i) (While t s) v v′′ h
  with evalT t v | inspect (evalT t) v

evalS⇐SWhileEvalRel (suc i) (While t s) .v′′ v′′ refl | VNil | [ f ]ⁱ =
  SWhileEvalWhileNil f

evalS⇐SWhileEvalRel (suc i) (While t s) v v′′ h
  | VCons v1 v2 | [ f ]ⁱ
  with evalS i s v | inspect (evalS i s) v

evalS⇐SWhileEvalRel (suc i) (While t s) v v′′ h
  | VCons v1 v2 | [ f ]ⁱ | just v′ | [ g ]ⁱ 
  = SWhileEvalWhileCons f
      (evalS⇐SWhileEvalRel i s v v′ g)
      (evalS⇐SWhileEvalRel i (While t s) v′ v′′ h)

evalS⇐SWhileEvalRel (suc i) (While t s) v v′′ ()
  | VCons v1 v2 | [ f ]ⁱ | nothing | [ g ]ⁱ

evalS⇐SWhileEvalRel (suc i) (While t s) v .VBottom refl | VBottom | [ f ]ⁱ =
  SWhileEvalWhileBottom f

-- evalS⇔SWhileEvalRel

evalS⇔SWhileEvalRel :
  ∀ s v v′ →
    SWhileEvalRel v s v′ ⇔
    (∃ λ (i : ℕ) → evalS i s v ≡ just v′)

evalS⇔SWhileEvalRel s v v′ =
  equivalence (evalS⇒SWhileEvalRel s v v′)
              (λ {(i , h) → evalS⇐SWhileEvalRel i s v v′ h})


----------------------------------------------------------
-- Evaluation semantics for KNF programs.
-- We add an extra parameter limiting the recursion depth,
-- in order to make functions total.
----------------------------------------------------------

-- evalKNFCore

evalKNFCore : (i : ℕ) (cond e : Trm) (v : Val) → Maybe Val
evalKNFCore′ : (i : ℕ) (cond e : Trm) (v : Val) (r : Val) → Maybe Val

evalKNFCore zero cond e v = nothing

evalKNFCore (suc i) cond e v =
  evalKNFCore′ i cond e v (evalT e v)

evalKNFCore′ i cond e v VNil =
  just v

evalKNFCore′ i cond e v (VCons v1 v2) =
  evalKNFCore i cond e (evalT e v)

evalKNFCore′ i cond e v VBottom =
  just VBottom

-- evalKNF

evalKNF : (i : ℕ) (knf : KNFProg) (v : Val) → Maybe Val

evalKNF i (NFProg initExp condExp bodyExp finalExp) v
  with evalKNFCore i condExp bodyExp (evalT initExp v)
... | nothing = nothing
... | just v′ = just (evalT finalExp v′)

---------------------------------------------------------
-- The executable KNF interpreter is correct with respect
-- to the relational semantics.
---------------------------------------------------------

-- evalKNFCore⇒SWhileEvalRel

evalKNFCore⇒SWhileEvalRel :
  ∀ cond e v v′ →
    SWhileEvalRel v (While cond (Assign e)) v′ →
    (∃ λ (i : ℕ) → evalKNFCore i cond e v ≡ just v′)

evalKNFCore⇒SWhileEvalRel cond e v v′ h = {!!}

-- evalKNFCore⇐SWhileEvalRel

evalKNFCore⇐SWhileEvalRel :
  ∀ i cond e v v′ →
    evalKNFCore i cond e v ≡ just v′ →
    SWhileEvalRel v (While cond (Assign e)) v′

evalKNFCore⇐SWhileEvalRel = {!!}

-- evalKNFCore⇔SWhileEvalRel

evalKNFCore⇔SWhileEvalRel :
  ∀ cond e v v′ →
    SWhileEvalRel v (While cond (Assign e)) v′ ⇔
    (∃ λ (i : ℕ) → evalKNFCore i cond e v ≡ just v′)

evalKNFCore⇔SWhileEvalRel cond e v v′ =
  equivalence (evalKNFCore⇒SWhileEvalRel cond e v v′)
              (λ {(i , h) → evalKNFCore⇐SWhileEvalRel i cond e v v′ h})

--
