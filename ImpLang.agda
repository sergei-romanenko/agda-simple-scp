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
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong; subst; inspect; module ≡-Reasoning)
  renaming ([_] to [_]ⁱ)

import Function.Related as Related

open import Data.Nat.Properties
  using (⊔-⊓-0-isCommutativeSemiringWithoutOne; m≤m⊔n; ≤⇒≤′)

open import Algebra.Structures
  using (module IsCommutativeSemiringWithoutOne)

open import Util
open import ExpLang
open import PositiveInfo

-- We embed the language of simple expressions inside a small
-- imperative language with assignments and while-loops (called here SWhile).

infix 4 var≔_ while[_]_
infixr 4 _//_

data Stmt : Set where
  var≔_    : (t : Trm) → Stmt
  _//_      : (s1 s2 : Stmt) → Stmt
  while[_]_ : (t : Trm) → (s : Stmt) → Stmt

-- Since this language is Turing-complete, we cannot specify
-- its evaluator as a total Agda function.
-- Thus we specify its semantics as a relation.

-- Big-step evaluation relation for SWhile programs

infix 3 _⊨_⇓_

data _⊨_⇓_ : Stmt → Val → Val → Set where
  ⇓-var≔ :
    ∀ {t v} → var≔ t ⊨ v ⇓ (⟦_⟧ t v) 
  ⇓-Seq :
    ∀ {s1 s2 v v′ v′′} →
    s1 ⊨ v ⇓ v′ → s2 ⊨ v′ ⇓ v′′ →
    s1 // s2 ⊨ v ⇓ v′′
  ⇓-WhileNil :
    ∀ {cond s v} →
    ⟦_⟧ cond v ≡ VNil →
    while[ cond ] s ⊨ v ⇓ v
  ⇓-WhileBottom :
    ∀ {cond s v} →
    ⟦_⟧ cond v ≡ VBottom →
    while[ cond ] s ⊨ v ⇓ VBottom
  ⇓-WhileCons :
    ∀ {cond s v v′ v′′ vh vt} →
    ⟦_⟧ cond v ≡ VCons vh vt →
    s ⊨ v ⇓ v′ → while[ cond ] s ⊨ v′ ⇓ v′′ →
    while[ cond ] s ⊨ v ⇓ v′′

-- A `KNF` program contains a single while loop.
-- This is an analog of Kleene's normal form (KNF) from recursion theory.
-- An analog of the "Kleene normal form" for SWhile programs
-- can be represented as a record of 4 simple expressions

record KNFProg : Set where
  constructor KNF
  field
    initExp  : Trm
    condExp  : Trm
    bodyExp  : Trm
    finalExp : Trm

open KNFProg public


-- Big-step evaluation relation for KNF programs

infix 4 [_]_⊨While_⇓_

data [_]_⊨While_⇓_ : Trm → Trm → Val → Val → Set where
  ⇓-WhileNil :
    ∀ {cond e v} →
    (≡VNil : ⟦_⟧ cond v ≡ VNil) →
    [ cond ] e ⊨While v ⇓ v    
  ⇓-WhileBottom :
    ∀ {cond e v} →
    (≡VBottom : ⟦_⟧ cond v ≡ VBottom) →
    [ cond ] e ⊨While v ⇓ VBottom
  ⇓-WhileCons :
    ∀ {cond e v v′ vh vt} →
    (≡VCons : ⟦_⟧ cond v ≡ VCons vh vt) →
    (h : [ cond ] e ⊨While ⟦_⟧ e v ⇓ v′) →
    [ cond ] e ⊨While v ⇓ v′

infix 3 _⊨KNF_⇓_

data _⊨KNF_⇓_ : KNFProg → Val → Val → Set where
  ⇓-eval :
    ∀ {init cond body final v v′} →
      [ cond ] body ⊨While (⟦_⟧ init v) ⇓ v′ →
      KNF init cond body final ⊨KNF v ⇓ ⟦_⟧ final v′

-- KNFtoProg

KNFtoProg : KNFProg → Stmt
KNFtoProg knf =
  var≔ initExp knf //
  while[ condExp knf ] var≔ bodyExp knf //
  var≔ finalExp knf

-----------------------------------------------------
-- _⊨KNF_⇓_ is correct with respect to _⊨_⇓_ .
-----------------------------------------------------

-- ⊨While⇒⊨

⊨While⇒⊨ :
  ∀ {cond e v v′} →
  [ cond ] e ⊨While v ⇓ v′ →
  while[ cond ] var≔ e ⊨ v ⇓ v′

-- ⊨While⇒⊨

⊨While⇒⊨ (⇓-WhileNil ≡VNil) =
  ⇓-WhileNil ≡VNil
⊨While⇒⊨ (⇓-WhileBottom ≡VBottom) =
  ⇓-WhileBottom ≡VBottom
⊨While⇒⊨ (⇓-WhileCons ≡VCons h) =
  ⇓-WhileCons ≡VCons ⇓-var≔ (⊨While⇒⊨ h)

-- ⊨KNF⇒⊨

⊨KNF⇒⊨ :
  ∀ {knf v v′} →
  knf ⊨KNF v ⇓ v′ → KNFtoProg knf ⊨ v ⇓ v′

⊨KNF⇒⊨ (⇓-eval h) =
  ⇓-Seq ⇓-var≔ (⇓-Seq (⊨While⇒⊨ h) ⇓-var≔)

-- ⊨⇒⊨While

⊨⇒⊨While :
  ∀ {cond e v v′} →
  while[ cond ] var≔ e ⊨ v ⇓ v′ →
  [ cond ] e ⊨While v ⇓ v′

⊨⇒⊨While (⇓-WhileNil ≡VNil) =
  ⇓-WhileNil ≡VNil
⊨⇒⊨While (⇓-WhileBottom ≡VBottom) =
  ⇓-WhileBottom ≡VBottom
⊨⇒⊨While (⇓-WhileCons ≡VCons ⇓-var≔ h) =
  ⇓-WhileCons ≡VCons (⊨⇒⊨While h)

-- ⊨⇒⊨KNF

⊨⇒⊨KNF :
  ∀ {knf v v′} →
  KNFtoProg knf ⊨ v ⇓ v′ → knf ⊨KNF v ⇓ v′

⊨⇒⊨KNF (⇓-Seq ⇓-var≔ (⇓-Seq h ⇓-var≔)) =
  ⇓-eval (⊨⇒⊨While h)

-- ⊨KNF⇔⊨

⊨KNF⇔⊨ :
  ∀ {knf v v′} →
  (knf ⊨KNF v ⇓ v′) ⇔ (KNFtoProg knf ⊨ v ⇓ v′)

⊨KNF⇔⊨ =
  equivalence ⊨KNF⇒⊨ ⊨⇒⊨KNF

-----------------------------------------------
-- Many optimizing transformations are valid
-- only if the condition of the loop is strict,
-- according to the following definition.
-----------------------------------------------

-- strictTrm

StrictTrm : Trm → Set
StrictTrm t = ⟦_⟧ t VBottom ≡ VBottom

-- strictKNF

StrictKNF : KNFProg → Set
StrictKNF knf = StrictTrm (condExp knf)

-- The strictness of terms in normal form is decidable.

-- strictNTrm

StrictNTrm : NTrm → Set
StrictNTrm nt = ⟦⌈_⌉⟧ nt VBottom ≡ VBottom

-- strictNTrm?

strictNTrm? : (nt : NTrm) → Dec (StrictNTrm nt)

strictNTrm? []ⁿ = no (λ ())

strictNTrm? (nt1 ∷ⁿ nt2) = no (λ ())

strictNTrm? (NSelCmp sels) = yes $ begin
  ⟦⌈_⌉⟧ (NSelCmp sels) VBottom
    ≡⟨ refl ⟩
  ⟦_⟧ ⟪ sels ⟫ VBottom
    ≡⟨ ⟦⟧∘⟪⟫ sels VBottom ⟩
  _!!_ VBottom sels
    ≡⟨ !!-VBottom sels ⟩
  VBottom
  ∎
  where open ≡-Reasoning

strictNTrm? (IfNilⁿ sels nt1 nt2) = yes $ begin
  ifNil (⟦_⟧ ⟪ sels ⟫ VBottom)
        (⟦⌈_⌉⟧ nt1 VBottom) (⟦⌈_⌉⟧ nt2 VBottom)
    ≡⟨ ifNil-cong (⟦⟧∘⟪⟫ sels VBottom) refl refl ⟩
  ifNil (_!!_ VBottom sels)
        (⟦⌈_⌉⟧ nt1 VBottom) (⟦⌈_⌉⟧ nt2 VBottom)
    ≡⟨ ifNil-cong (!!-VBottom sels) refl refl ⟩
  VBottom
  ∎
  where open ≡-Reasoning

strictNTrm? ↯ⁿ = yes refl

-- The strictness of terms in normal form is decidable.
-- We just normalize the term and then apply `strictNTrm?`.

-- strictTrm?

strictTrm? : (t : Trm) → Dec (StrictTrm t)
strictTrm? t
  rewrite P.sym $ ⟦⌈⌉⟧∘normConv t VBottom
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

-- exec

exec : (d : ℕ) (s : Stmt) (v : Val) → Maybe Val
exec-While :
  (d : ℕ) (t : Trm) (s : Stmt) (v : Val) (r : Val) → Maybe Val

exec zero s v = nothing
exec (suc d) (var≔ t) v = just (⟦_⟧ t v)
exec (suc d) (s1 // s2) v =
  exec d s1 v >>= exec d s2
exec (suc d) (while[ t ] s) v =
  exec-While d t s v (⟦_⟧ t v)

exec-While d t s v VNil =
  just v

exec-While d t s v (VCons v1 v2) =
  exec d s v >>= exec d (while[ t ] s)

exec-While d t s v VBottom = just VBottom

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

-- exec-mono

exec-mono : (s : Stmt) (i j : ℕ) → i ≤′ j → (v v′ : Val) →
    exec i s v ≡ just v′ → exec j s v ≡ just v′

exec-mono s zero j i≤′j v v′ ()

exec-mono s (suc i) zero () v v′ h

exec-mono s (suc .j) (suc j) ≤′-refl v v′ h = h

exec-mono s (suc i) (suc j) (≤′-step m≤′n) v v′′ h = helper s h
  where
  helper : (s : Stmt) →
    exec (suc i) s v ≡ just v′′ → exec (suc j) s v ≡ just v′′

  helper (var≔ t) h′ = h′

  helper (s1 // s2) h′ with exec i s1 v | inspect (exec i s1) v
  helper (s1 // s2) h′ | just v′ | [ g₁ ]ⁱ
    rewrite exec-mono s1 i j (<′⇨≤′ m≤′n) v v′ g₁
    = exec-mono s2 i j (<′⇨≤′ m≤′n) v′ v′′ h′
  helper (s1 // s2) () | nothing | [ g₁ ]ⁱ

  helper (while[ t ] s') h′ with ⟦_⟧ t v
  helper (while[ t ] s') h′ | VNil = h′
  helper (while[ t ] s') h′ | VCons v1 v2
    with exec i s' v | inspect (exec i s') v
  ... | just v′ | [ g ]ⁱ
    rewrite exec-mono s' i j (<′⇨≤′ m≤′n) v v′ g
    = exec-mono (while[ t ] s') i j (<′⇨≤′ m≤′n) v′ v′′ h′
  helper (while[ t ] s') () | VCons v1 v2 | nothing | [ g ]ⁱ
  helper (while[ t ] s') h′ | VBottom = h′

-- ⇓-⇒exec

⇓-⇒exec :
  ∀ s v v′ →
    s ⊨ v ⇓ v′ →
    (∃ λ (i : ℕ) → exec i s v ≡ just v′)

⇓-⇒exec (var≔ t) v .(⟦_⟧ t v) ⇓-var≔ =
  suc zero , refl

⇓-⇒exec (s1 // s2) v v′′ (⇓-Seq {v′ = v′} h₁ h₂)
  with ⇓-⇒exec s1 v v′ h₁ | ⇓-⇒exec s2 v′ v′′ h₂
... | i₁ , g₁ | i₂ , g₂ = suc (i₁ ⊔ i₂) , (begin
    exec (i₁ ⊔ i₂) s1 v >>= exec (i₁ ⊔ i₂) s2
      ≡⟨ cong (flip _>>=_ (exec (i₁ ⊔ i₂) s2))
              (exec-mono s1 i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) v v′ g₁) ⟩
    exec (i₁ ⊔ i₂) s2 v′
      ≡⟨ exec-mono s2 i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) v′ v′′ g₂ ⟩
    just v′′
    ∎)
  where open ≡-Reasoning

⇓-⇒exec (while[ t ] s) .v′′ v′′ (⇓-WhileNil ≡VNil) =
  suc zero , (begin
    exec-While zero t s v′′ (⟦_⟧ t v′′)
      ≡⟨ cong (exec-While zero t s v′′) ≡VNil ⟩
    just v′′
    ∎)
  where open ≡-Reasoning

⇓-⇒exec (while[ t ] s) v .VBottom (⇓-WhileBottom ≡VBottom) =
  suc zero , (begin
    exec-While zero t s v (⟦_⟧ t v)
      ≡⟨ cong (exec-While zero t s v) ≡VBottom ⟩
    just VBottom
    ∎)
  where open ≡-Reasoning

⇓-⇒exec (while[ t ] s) v v′′
  (⇓-WhileCons {v′ = v′} ≡VCons h₁ h₂)
  with ⇓-⇒exec s v v′ h₁ | ⇓-⇒exec (while[ t ] s) v′ v′′ h₂
... | i₁ , g₁ | i₂ , g₂ = suc (i₁ ⊔ i₂) , (begin
    exec-While (i₁ ⊔ i₂) t s v (⟦_⟧ t v)
      ≡⟨ cong (exec-While (i₁ ⊔ i₂) t s v) ≡VCons ⟩
    exec (i₁ ⊔ i₂) s v >>= exec (i₁ ⊔ i₂) (while[ t ] s)
      ≡⟨ cong (flip _>>=_ (exec (i₁ ⊔ i₂) (while[ t ] s)))
              (exec-mono s i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) v v′ g₁) ⟩
    exec (i₁ ⊔ i₂) (while[ t ] s) v′
      ≡⟨ exec-mono (while[ t ] s) i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) v′ v′′ g₂ ⟩
    just v′′
    ∎)
  where open ≡-Reasoning

-- exec⇒-⇓

exec⇒-⇓ :
  ∀ i s v v′ →
    exec i s v ≡ just v′ →
    s ⊨ v ⇓ v′

exec⇒-⇓ zero s v v′′ ()

exec⇒-⇓ (suc i) (var≔ t) v .(⟦_⟧ t v) refl =
  ⇓-var≔

exec⇒-⇓ (suc i) (s1 // s2) v v′′ h
  with exec i s1 v | inspect (exec i s1) v

exec⇒-⇓ (suc i) (s1 // s2) v v′′ h
  | just v′ | [ g₁ ]ⁱ
  = ⇓-Seq (exec⇒-⇓ i s1 v v′ g₁)
          (exec⇒-⇓ i s2 v′ v′′ h)

exec⇒-⇓ (suc i) (s1 // s2) v v′′ ()
  | nothing | [ g₁ ]ⁱ

exec⇒-⇓ (suc i) (while[ t ] s) v v′′ h
  with ⟦_⟧ t v | inspect (⟦_⟧ t) v

exec⇒-⇓ (suc i) (while[ t ] s) .v′′ v′′ refl
  | VNil | [ f ]ⁱ =
  ⇓-WhileNil f

exec⇒-⇓ (suc i) (while[ t ] s) v v′′ h
  | VCons v1 v2 | [ f ]ⁱ
  with exec i s v | inspect (exec i s) v

exec⇒-⇓ (suc i) (while[ t ] s) v v′′ h
  | VCons v1 v2 | [ f ]ⁱ | just v′ | [ g ]ⁱ 
  = ⇓-WhileCons f (exec⇒-⇓ i s v v′ g)
                  (exec⇒-⇓ i (while[ t ] s) v′ v′′ h)

exec⇒-⇓ (suc i) (while[ t ] s) v v′′ ()
  | VCons v1 v2 | [ f ]ⁱ | nothing | [ g ]ⁱ

exec⇒-⇓ (suc i) (while[ t ] s) v .VBottom refl | VBottom | [ f ]ⁱ =
  ⇓-WhileBottom f

-- ⇓-⇔exec

⇓-⇔exec :
  ∀ {s v v′} →
    (s ⊨ v ⇓ v′) ⇔
    (∃ λ (i : ℕ) → exec i s v ≡ just v′)

⇓-⇔exec {s} {v} {v′} =
  equivalence (⇓-⇒exec s v v′)
              (λ {(i , h) → exec⇒-⇓ i s v v′ h})


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
  evalKNFCore′ i cond e v (⟦_⟧ cond v)

evalKNFCore′ i cond e v VNil =
  just v

evalKNFCore′ i cond e v (VCons v1 v2) =
  evalKNFCore i cond e (⟦_⟧ e v)

evalKNFCore′ i cond e v VBottom =
  just VBottom

-- evalKNF

evalKNF : (i : ℕ) (knf : KNFProg) (v : Val) → Maybe Val
evalKNF′ : (finalExp : Trm) (r : Maybe Val) → Maybe Val

evalKNF i (KNF initExp condExp bodyExp finalExp) v =
  evalKNF′ finalExp (evalKNFCore i condExp bodyExp (⟦_⟧ initExp v))

evalKNF′ finalExp (just v′) = just (⟦_⟧ finalExp v′)
evalKNF′ finalExp nothing = nothing


---------------------------------------------------------
-- The executable KNF interpreter is correct with respect
-- to the relational KNF semantics.
---------------------------------------------------------

-- ⊨While⇒evalKNFCore

⊨While⇒evalKNFCore :
  ∀ {cond e v v′} →
    [ cond ] e ⊨While v ⇓ v′ →
    (∃ λ (i : ℕ) → evalKNFCore i cond e v ≡ just v′)

⊨While⇒evalKNFCore (⇓-WhileNil {cond} {e} {v} ≡VNil) =
  suc zero , (begin
  evalKNFCore′ 0 cond e v (⟦_⟧ cond v)
    ≡⟨ cong (evalKNFCore′ 0 cond e v) ≡VNil ⟩
  evalKNFCore′ 0 cond e v VNil
    ≡⟨ refl ⟩
  just v
  ∎)
  where open ≡-Reasoning

⊨While⇒evalKNFCore (⇓-WhileBottom {cond} {e} {v} ≡VBottom) =
  (suc zero) , (begin
  evalKNFCore′ 0 cond e v (⟦_⟧ cond v)
    ≡⟨ cong (evalKNFCore′ 0 cond e v) ≡VBottom ⟩
  evalKNFCore′ 0 cond e v VBottom
    ≡⟨ refl ⟩
  just VBottom
  ∎)
  where open ≡-Reasoning

⊨While⇒evalKNFCore (⇓-WhileCons {cond} {e} {v} {v′′} {vh} {vt} ≡VCons h)
  with ⊨While⇒evalKNFCore h
... | i , g = suc i , (begin
  evalKNFCore′ i cond e v (⟦_⟧ cond v)
    ≡⟨ cong (evalKNFCore′ i cond e v) ≡VCons ⟩
  evalKNFCore′ i cond e v (VCons vt vt)
    ≡⟨ g ⟩
  just v′′
  ∎)
  where open ≡-Reasoning

-- ⊨KNF⇒evalKNF

⊨KNF⇒evalKNF :
  ∀ {knf v v′} →
    knf ⊨KNF v ⇓ v′ →
    (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′)

⊨KNF⇒evalKNF (⇓-eval {init} {cond} {body} {final} {v} {v′} h)
  with ⊨While⇒evalKNFCore h
... | i , g = i , (begin
  evalKNF′ final (evalKNFCore i cond body (⟦_⟧ init v))
    ≡⟨ cong (evalKNF′ final) g ⟩
  evalKNF′ final (just v′)
    ≡⟨ refl ⟩
  just (⟦_⟧ final v′)
  ∎)
  where open ≡-Reasoning

-- evalKNFCore⇒⊨While

evalKNFCore⇒⊨While :
  ∀ i {cond e v v′} →
    evalKNFCore i cond e v ≡ just v′ →
    [ cond ] e ⊨While v ⇓ v′

evalKNFCore⇒⊨While zero ()

evalKNFCore⇒⊨While (suc i) {cond} {e} {v} {v′} h
  with ⟦_⟧ cond v | inspect (⟦_⟧ cond) v

evalKNFCore⇒⊨While (suc i) refl | VNil | [ ≡VNil ]ⁱ =
  ⇓-WhileNil ≡VNil

evalKNFCore⇒⊨While (suc i) h | VCons v1 v2  | [ ≡VCons ]ⁱ =
  ⇓-WhileCons ≡VCons (evalKNFCore⇒⊨While i h)

evalKNFCore⇒⊨While (suc i) refl | VBottom  | [ ≡VBottom ]ⁱ =
  ⇓-WhileBottom ≡VBottom

-- evalKNF⇒⊨KNF

evalKNF⇒⊨KNF :
  ∀ i {knf v v′} →
    evalKNF i knf v ≡ just v′ →
    knf ⊨KNF v ⇓ v′

evalKNF⇒⊨KNF i {KNF init cond body final} {v} {v′} h
  with evalKNFCore i cond body (⟦_⟧ init v)
     | inspect (evalKNFCore i cond body) (⟦_⟧ init v)

evalKNF⇒⊨KNF i {KNF init cond body final} refl | just v′ | [ ≡v′ ]ⁱ =
  ⇓-eval (evalKNFCore⇒⊨While i ≡v′)

evalKNF⇒⊨KNF i {KNF init cond body final} () | nothing | [ ≡v′ ]ⁱ

-- ⊨KNF⇔evalKNF

⊨KNF⇔evalKNF :
  ∀ {knf v v′} →
    (knf ⊨KNF v ⇓ v′) ⇔
    (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′)

⊨KNF⇔evalKNF =
  equivalence ⊨KNF⇒evalKNF
              (λ {(i , h) → evalKNF⇒⊨KNF i h})


---------------------------------------------------------
-- The executable KNF interpreter is correct with respect
-- to the SWhile interpreter.
---------------------------------------------------------

-- evalKNF⇔exec

evalKNF⇔exec :
  ∀ knf v v′ →
    ∃ (λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
    ∃ (λ (j : ℕ) → exec j (KNFtoProg knf) v ≡ just v′)

evalKNF⇔exec knf v v′ =
  (∃ (λ (i : ℕ) → evalKNF i knf v ≡ just v′))
    ∼⟨ sym $ ⊨KNF⇔evalKNF ⟩
  knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF⇔⊨ ⟩
  KNFtoProg knf ⊨ v ⇓ v′
    ∼⟨ ⇓-⇔exec ⟩
  (∃ (λ (j : ℕ) → exec j (KNFtoProg knf) v ≡ just v′))
  ∎
  where open Related.EquationalReasoning


--
