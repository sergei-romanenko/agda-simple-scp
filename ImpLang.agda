--
-- A Turing-complete Imperative Language
--

module ImpLang where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Empty

open import Function
open import Function.Equivalence
  using (_⇔_; equivalence)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; trans; cong; subst; inspect; module ≡-Reasoning)
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

-----------------------------------------------------
-- SWhile language
-----------------------------------------------------

infix 6 var≔_ while[_]_
infixr 5 _//_

data Stmt : Set where
  var≔_    : (t : Trm) → Stmt
  _//_      : (s1 s2 : Stmt) → Stmt
  while[_]_ : (t : Trm) → (s : Stmt) → Stmt

-- Since this language is Turing-complete, we cannot specify
-- its evaluator as a total Agda function.
-- Thus we specify its semantics as a relation.

-----------------------------------------------------
-- Big-step evaluation relation for SWhile programs
-----------------------------------------------------

infix 4 _⊨_⇓_

data _⊨_⇓_ : Stmt → Val → Val → Set where
  ⇓-var≔ :
    ∀ {t v} → var≔ t ⊨ v ⇓ (⟦ t ⟧ v) 
  ⇓-Seq :
    ∀ {s1 s2 v v′ v′′} →
    s1 ⊨ v ⇓ v′ → s2 ⊨ v′ ⇓ v′′ →
    s1 // s2 ⊨ v ⇓ v′′
  ⇓-WhileNil :
    ∀ {cond s v} →
    ⟦ cond ⟧ v ≡ []ˣ →
    while[ cond ] s ⊨ v ⇓ v
  ⇓-WhileBottom :
    ∀ {cond s v} →
    ⟦ cond ⟧ v ≡ ↯ˣ →
    while[ cond ] s ⊨ v ⇓ ↯ˣ
  ⇓-WhileCons :
    ∀ {cond s v v′ v′′ vh vt} →
    ⟦ cond ⟧ v ≡ vh ∷ˣ vt →
    s ⊨ v ⇓ v′ → while[ cond ] s ⊨ v′ ⇓ v′′ →
    while[ cond ] s ⊨ v ⇓ v′′

-----------------------------------------------------
-- _⊨_⇓_ is deterministic
-----------------------------------------------------

-- ⊨-det

⊨-det :
  {s : Stmt} {v v′ v′′ : Val} →
  s ⊨ v ⇓ v′ → s ⊨ v ⇓ v′′ → v′ ≡ v′′

⊨-det ⇓-var≔ ⇓-var≔ = refl

⊨-det (⇓-Seq h₁ h₂) (⇓-Seq g₁ g₂)
  rewrite ⊨-det h₁ g₁ | ⊨-det h₂ g₂
  = refl

⊨-det (⇓-WhileNil h) (⇓-WhileNil g) = refl

⊨-det (⇓-WhileNil f₁) (⇓-WhileBottom f₂) =
  ⊥-elim (↯ˣ≢[]ˣ (trans (P.sym f₂) f₁))

⊨-det (⇓-WhileNil f₁) (⇓-WhileCons f₂ g₁ g₂) =
  ⊥-elim (∷ˣ≢[]ˣ (trans (P.sym f₂) f₁))

⊨-det (⇓-WhileBottom f₁) (⇓-WhileNil f₂) =
  ⊥-elim (↯ˣ≢[]ˣ (trans (P.sym f₁) f₂))

⊨-det (⇓-WhileBottom f₁) (⇓-WhileBottom f₂) = refl

⊨-det (⇓-WhileBottom f₁) (⇓-WhileCons f₂ g₁ g₂) =
  ⊥-elim (∷ˣ≢↯ˣ (trans (P.sym f₂) f₁))

⊨-det (⇓-WhileCons f₁ h₁ h₂) (⇓-WhileNil f₂) =
  ⊥-elim (∷ˣ≢[]ˣ (trans (P.sym f₁) f₂))

⊨-det (⇓-WhileCons f₁ h₁ h₂) (⇓-WhileBottom f₂) =
  ⊥-elim (∷ˣ≢↯ˣ (trans (P.sym f₁) f₂))

⊨-det (⇓-WhileCons f₁ h₁ h₂) (⇓-WhileCons f₂ g₁ g₂)
  rewrite ⊨-det h₁ g₁ | ⊨-det h₂ g₂
  = refl


-- A `KNF` program contains a single while loop.
-- This is an analog of Kleene's normal form (KNF) from recursion theory.
-- An analog of the "Kleene normal form" for SWhile programs
-- can be represented as a record of 4 simple expressions

-----------------------------------------------------
-- KNF language
-----------------------------------------------------

record KNFProg : Set where
  constructor KNF
  field
    initExp  : Trm
    condExp  : Trm
    bodyExp  : Trm
    finalExp : Trm

open KNFProg public


-----------------------------------------------------
-- Big-step evaluation relation for KNF programs
-----------------------------------------------------

infix 4 [_]_⊨While_⇓_

data [_]_⊨While_⇓_ : Trm → Trm → Val → Val → Set where
  ⇓-WhileNil :
    ∀ {cond e v} →
    (≡[]ˣ : ⟦ cond ⟧ v ≡ []ˣ) →
    [ cond ] e ⊨While v ⇓ v    
  ⇓-WhileBottom :
    ∀ {cond e v} →
    (≡↯ˣ : ⟦ cond ⟧ v ≡ ↯ˣ) →
    [ cond ] e ⊨While v ⇓ ↯ˣ
  ⇓-WhileCons :
    ∀ {cond e v v′ vh vt} →
    (≡∷ˣ : ⟦ cond ⟧ v ≡ vh ∷ˣ vt) →
    (h : [ cond ] e ⊨While ⟦ e ⟧ v ⇓ v′) →
    [ cond ] e ⊨While v ⇓ v′

infix 4 _⊨KNF_⇓_

data _⊨KNF_⇓_ : KNFProg → Val → Val → Set where
  ⇓-eval :
    ∀ {init cond body final v v′} →
      [ cond ] body ⊨While (⟦ init ⟧ v) ⇓ v′ →
      KNF init cond body final ⊨KNF v ⇓ ⟦ final ⟧ v′

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

⊨While⇒⊨ (⇓-WhileNil ≡[]ˣ) =
  ⇓-WhileNil ≡[]ˣ
⊨While⇒⊨ (⇓-WhileBottom ≡↯ˣ) =
  ⇓-WhileBottom ≡↯ˣ
⊨While⇒⊨ (⇓-WhileCons ≡∷ˣ h) =
  ⇓-WhileCons ≡∷ˣ ⇓-var≔ (⊨While⇒⊨ h)

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

⊨⇒⊨While (⇓-WhileNil ≡[]ˣ) =
  ⇓-WhileNil ≡[]ˣ
⊨⇒⊨While (⇓-WhileBottom ≡↯ˣ) =
  ⇓-WhileBottom ≡↯ˣ
⊨⇒⊨While (⇓-WhileCons ≡∷ˣ ⇓-var≔ h) =
  ⇓-WhileCons ≡∷ˣ (⊨⇒⊨While h)

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

-----------------------------------------------------
-- _⊨KNF_⇓_ is deterministic.
-----------------------------------------------------

-- ⊨KNF-det

⊨KNF-det :
  ∀ {knf v v′ v′′} →
  knf ⊨KNF v ⇓ v′ → knf ⊨KNF v ⇓ v′′ → v′ ≡ v′′

⊨KNF-det {knf} {v} {v′} {v′′} h₁ h₂ =
  ⊨-det (⊨KNF⇒⊨ h₁) (⊨KNF⇒⊨ h₂)

-----------------------------------------------
-- Many optimizing transformations are valid
-- only if the condition of the loop is strict,
-- according to the following definition.
-----------------------------------------------

-- strictTrm

StrictTrm : Trm → Set
StrictTrm t = ⟦ t ⟧ ↯ˣ ≡ ↯ˣ

-- strictKNF

StrictKNF : KNFProg → Set
StrictKNF knf = StrictTrm (condExp knf)

-- The strictness of terms in normal form is decidable.

-- strictNTrm

StrictNTrm : NTrm → Set
StrictNTrm nt = ⟦⌈ nt ⌉⟧ ↯ˣ ≡ ↯ˣ

-- strictNTrm?

strictNTrm? : (nt : NTrm) → Dec (StrictNTrm nt)

strictNTrm? []ⁿ = no (λ ())

strictNTrm? (nt1 ∷ⁿ nt2) = no (λ ())

strictNTrm? ⟪ sels ⟫ⁿ = yes $ begin
  ⟦⌈ ⟪ sels ⟫ⁿ ⌉⟧ ↯ˣ
    ≡⟨ refl ⟩
  ⟦ ⟪ sels ⟫ ⟧ ↯ˣ
    ≡⟨ ⟦⟧∘⟪⟫ sels ↯ˣ ⟩
  ↯ˣ !! sels
    ≡⟨ ↯ˣ-!! sels ⟩
  ↯ˣ
  ∎
  where open ≡-Reasoning

strictNTrm? (IfNilⁿ sels nt1 nt2) = yes $ begin
  ifNil (⟦ ⟪ sels ⟫ ⟧ ↯ˣ)
        (⟦⌈ nt1 ⌉⟧ ↯ˣ) (⟦⌈ nt2 ⌉⟧ ↯ˣ)
    ≡⟨ ifNil-cong (⟦⟧∘⟪⟫ sels ↯ˣ) refl refl ⟩
  ifNil (↯ˣ !! sels)
        (⟦⌈ nt1 ⌉⟧ ↯ˣ) (⟦⌈ nt2 ⌉⟧ ↯ˣ)
    ≡⟨ ifNil-cong (↯ˣ-!! sels) refl refl ⟩
  ↯ˣ
  ∎
  where open ≡-Reasoning

strictNTrm? ↯ⁿ = yes refl

-- The strictness of terms in normal form is decidable.
-- We just normalize the term and then apply `strictNTrm?`.

-- strictTrm?

strictTrm? : (t : Trm) → Dec (StrictTrm t)
strictTrm? t
  rewrite P.sym $ ⟦⌈⌉⟧∘⌋⌊ t ↯ˣ
  = strictNTrm? ⌋ t ⌊

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
exec (suc d) (var≔ t) v = just (⟦ t ⟧ v)
exec (suc d) (s1 // s2) v =
  exec d s1 v >>= exec d s2
exec (suc d) (while[ t ] s) v =
  exec-While d t s v (⟦ t ⟧ v)

exec-While d t s v []ˣ =
  just v

exec-While d t s v (v1 ∷ˣ v2) =
  exec d s v >>= exec d (while[ t ] s)

exec-While d t s v ↯ˣ = just ↯ˣ

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

  helper (while[ t ] s') h′ with ⟦ t ⟧ v
  helper (while[ t ] s') h′ | []ˣ = h′
  helper (while[ t ] s') h′ | v1 ∷ˣ v2
    with exec i s' v | inspect (exec i s') v
  ... | just v′ | [ g ]ⁱ
    rewrite exec-mono s' i j (<′⇨≤′ m≤′n) v v′ g
    = exec-mono (while[ t ] s') i j (<′⇨≤′ m≤′n) v′ v′′ h′
  helper (while[ t ] s') () | v1 ∷ˣ v2 | nothing | [ g ]ⁱ
  helper (while[ t ] s') h′ | ↯ˣ = h′

-- ⇓-⇒exec

⇓-⇒exec :
  ∀ s v v′ →
    s ⊨ v ⇓ v′ →
    (∃ λ (i : ℕ) → exec i s v ≡ just v′)

⇓-⇒exec (var≔ t) v .(⟦ t ⟧ v) ⇓-var≔ =
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

⇓-⇒exec (while[ t ] s) .v′′ v′′ (⇓-WhileNil ≡[]ˣ) =
  suc zero , (begin
    exec-While zero t s v′′ (⟦ t ⟧ v′′)
      ≡⟨ cong (exec-While zero t s v′′) ≡[]ˣ ⟩
    just v′′
    ∎)
  where open ≡-Reasoning

⇓-⇒exec (while[ t ] s) v .↯ˣ (⇓-WhileBottom ≡↯ˣ) =
  suc zero , (begin
    exec-While zero t s v (⟦ t ⟧ v)
      ≡⟨ cong (exec-While zero t s v) ≡↯ˣ ⟩
    just ↯ˣ
    ∎)
  where open ≡-Reasoning

⇓-⇒exec (while[ t ] s) v v′′
  (⇓-WhileCons {v′ = v′} ≡∷ˣ h₁ h₂)
  with ⇓-⇒exec s v v′ h₁ | ⇓-⇒exec (while[ t ] s) v′ v′′ h₂
... | i₁ , g₁ | i₂ , g₂ = suc (i₁ ⊔ i₂) , (begin
    exec-While (i₁ ⊔ i₂) t s v (⟦ t ⟧ v)
      ≡⟨ cong (exec-While (i₁ ⊔ i₂) t s v) ≡∷ˣ ⟩
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

exec⇒-⇓ (suc i) (var≔ t) v .(⟦ t ⟧ v) refl =
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
  with ⟦ t ⟧ v | inspect ⟦ t ⟧ v

exec⇒-⇓ (suc i) (while[ t ] s) .v′′ v′′ refl
  | []ˣ | [ f ]ⁱ =
  ⇓-WhileNil f

exec⇒-⇓ (suc i) (while[ t ] s) v v′′ h
  | v1 ∷ˣ v2 | [ f ]ⁱ
  with exec i s v | inspect (exec i s) v

exec⇒-⇓ (suc i) (while[ t ] s) v v′′ h
  | v1 ∷ˣ v2 | [ f ]ⁱ | just v′ | [ g ]ⁱ 
  = ⇓-WhileCons f (exec⇒-⇓ i s v v′ g)
                  (exec⇒-⇓ i (while[ t ] s) v′ v′′ h)

exec⇒-⇓ (suc i) (while[ t ] s) v v′′ ()
  | v1 ∷ˣ v2 | [ f ]ⁱ | nothing | [ g ]ⁱ

exec⇒-⇓ (suc i) (while[ t ] s) v .↯ˣ refl | ↯ˣ | [ f ]ⁱ =
  ⇓-WhileBottom f

-- ⇓-⇔exec

⇓-⇔exec :
  ∀ {s v v′} →
    (s ⊨ v ⇓ v′) ⇔
    (∃ λ (i : ℕ) → exec i s v ≡ just v′)

⇓-⇔exec {s} {v} {v′} =
  equivalence (⇓-⇒exec s v v′)
              (λ {(i , h) → exec⇒-⇓ i s v v′ h})


-----------------------------------------------------
-- exec is deterministic
-----------------------------------------------------

-- exec-det

exec-det :
  ∀ {s v v′ v′′} →
    (∃ λ (i : ℕ) → exec i s v ≡ just v′) →
    (∃ λ (i′ : ℕ) → exec i′ s v ≡ just v′′) →
    v′ ≡ v′′

exec-det {s} {v} {v′} {v′′} (i , h₁) (i′ , h₂) =
  ⊨-det (exec⇒-⇓ i s v v′ h₁) (exec⇒-⇓ i′ s v v′′ h₂)

----------------------------------------------------------
-- Evaluation semantics for KNF programs.
-- We add an extra parameter limiting the recursion depth,
-- in order to make functions total.
----------------------------------------------------------

-- execKNFCore

execKNFCore : (i : ℕ) (cond e : Trm) (v : Val) → Maybe Val
execKNFCore′ : (i : ℕ) (cond e : Trm) (v : Val) (r : Val) → Maybe Val

execKNFCore zero cond e v = nothing

execKNFCore (suc i) cond e v =
  execKNFCore′ i cond e v (⟦ cond ⟧ v)

execKNFCore′ i cond e v []ˣ =
  just v

execKNFCore′ i cond e v (v1 ∷ˣ v2) =
  execKNFCore i cond e (⟦ e ⟧ v)

execKNFCore′ i cond e v ↯ˣ =
  just ↯ˣ

-- execKNF

execKNF : (i : ℕ) (knf : KNFProg) (v : Val) → Maybe Val
execKNF′ : (final : Trm) (r : Maybe Val) → Maybe Val

execKNF i (KNF init cond body final) v =
  execKNF′ final (execKNFCore i cond body (⟦ init ⟧ v))

execKNF′ final (just v′) = just (⟦ final ⟧ v′)
execKNF′ final nothing = nothing


---------------------------------------------------------
-- The executable KNF interpreter is correct with respect
-- to the relational KNF semantics.
---------------------------------------------------------

-- ⊨While⇒execKNFCore

⊨While⇒execKNFCore :
  ∀ {cond e v v′} →
    [ cond ] e ⊨While v ⇓ v′ →
    (∃ λ (i : ℕ) → execKNFCore i cond e v ≡ just v′)

⊨While⇒execKNFCore (⇓-WhileNil {cond} {e} {v} ≡[]ˣ) =
  suc zero , (begin
  execKNFCore′ 0 cond e v (⟦ cond ⟧ v)
    ≡⟨ cong (execKNFCore′ 0 cond e v) ≡[]ˣ ⟩
  execKNFCore′ 0 cond e v []ˣ
    ≡⟨ refl ⟩
  just v
  ∎)
  where open ≡-Reasoning

⊨While⇒execKNFCore (⇓-WhileBottom {cond} {e} {v} ≡↯ˣ) =
  (suc zero) , (begin
  execKNFCore′ 0 cond e v (⟦ cond ⟧ v)
    ≡⟨ cong (execKNFCore′ 0 cond e v) ≡↯ˣ ⟩
  execKNFCore′ 0 cond e v ↯ˣ
    ≡⟨ refl ⟩
  just ↯ˣ
  ∎)
  where open ≡-Reasoning

⊨While⇒execKNFCore (⇓-WhileCons {cond} {e} {v} {v′′} {vh} {vt} ≡∷ˣ h)
  with ⊨While⇒execKNFCore h
... | i , g = suc i , (begin
  execKNFCore′ i cond e v (⟦ cond ⟧ v)
    ≡⟨ cong (execKNFCore′ i cond e v) ≡∷ˣ ⟩
  execKNFCore′ i cond e v (vt ∷ˣ vt)
    ≡⟨ g ⟩
  just v′′
  ∎)
  where open ≡-Reasoning

-- ⊨KNF⇒execKNF

⊨KNF⇒execKNF :
  ∀ {knf v v′} →
    knf ⊨KNF v ⇓ v′ →
    (∃ λ (i : ℕ) → execKNF i knf v ≡ just v′)

⊨KNF⇒execKNF (⇓-eval {init} {cond} {body} {final} {v} {v′} h)
  with ⊨While⇒execKNFCore h
... | i , g = i , (begin
  execKNF′ final (execKNFCore i cond body (⟦ init ⟧ v))
    ≡⟨ cong (execKNF′ final) g ⟩
  execKNF′ final (just v′)
    ≡⟨ refl ⟩
  just (⟦ final ⟧ v′)
  ∎)
  where open ≡-Reasoning

-- execKNFCore⇒⊨While

execKNFCore⇒⊨While :
  ∀ i {cond e v v′} →
    execKNFCore i cond e v ≡ just v′ →
    [ cond ] e ⊨While v ⇓ v′

execKNFCore⇒⊨While zero ()

execKNFCore⇒⊨While (suc i) {cond} {e} {v} {v′} h
  with ⟦ cond ⟧ v | inspect ⟦ cond ⟧ v

execKNFCore⇒⊨While (suc i) refl | []ˣ | [ ≡[]ˣ ]ⁱ =
  ⇓-WhileNil ≡[]ˣ

execKNFCore⇒⊨While (suc i) h | v1 ∷ˣ v2  | [ ≡∷ˣ ]ⁱ =
  ⇓-WhileCons ≡∷ˣ (execKNFCore⇒⊨While i h)

execKNFCore⇒⊨While (suc i) refl | ↯ˣ  | [ ≡↯ˣ ]ⁱ =
  ⇓-WhileBottom ≡↯ˣ

-- execKNF⇒⊨KNF

execKNF⇒⊨KNF :
  ∀ i {knf v v′} →
    execKNF i knf v ≡ just v′ →
    knf ⊨KNF v ⇓ v′

execKNF⇒⊨KNF i {KNF init cond body final} {v} {v′} h
  with execKNFCore i cond body (⟦ init ⟧ v)
     | inspect (execKNFCore i cond body) (⟦ init ⟧ v)

execKNF⇒⊨KNF i {KNF init cond body final} refl | just v′ | [ ≡v′ ]ⁱ =
  ⇓-eval (execKNFCore⇒⊨While i ≡v′)

execKNF⇒⊨KNF i {KNF init cond body final} () | nothing | [ ≡v′ ]ⁱ

-- ⊨KNF⇔execKNF

⊨KNF⇔execKNF :
  ∀ {knf v v′} →
    (knf ⊨KNF v ⇓ v′) ⇔
    (∃ λ (i : ℕ) → execKNF i knf v ≡ just v′)

⊨KNF⇔execKNF =
  equivalence ⊨KNF⇒execKNF
              (λ {(i , h) → execKNF⇒⊨KNF i h})


---------------------------------------------------------
-- The executable KNF interpreter is correct with respect
-- to the SWhile interpreter.
---------------------------------------------------------

-- execKNF⇔exec

execKNF⇔exec :
  ∀ knf v v′ →
    ∃ (λ (i : ℕ) → execKNF i knf v ≡ just v′) ⇔
    ∃ (λ (j : ℕ) → exec j (KNFtoProg knf) v ≡ just v′)

execKNF⇔exec knf v v′ =
  (∃ (λ (i : ℕ) → execKNF i knf v ≡ just v′))
    ∼⟨ sym $ ⊨KNF⇔execKNF ⟩
  knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF⇔⊨ ⟩
  KNFtoProg knf ⊨ v ⇓ v′
    ∼⟨ ⇓-⇔exec ⟩
  (∃ (λ (j : ℕ) → exec j (KNFtoProg knf) v ≡ just v′))
  ∎
  where open Related.EquationalReasoning


--
