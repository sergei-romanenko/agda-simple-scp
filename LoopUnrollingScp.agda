--
-- Simple supercompiler using loop unrolling
--

module LoopUnrollingScp where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Product
  hiding (map)
open import Data.Sum

open import Function
open import Function.Equivalence as Equiv
  using (module Equivalence; _⇔_; equivalence)

open import Relation.Nullary
open import Relation.Nullary.Decidable
  using (⌊_⌋)

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; trans; cong; subst; inspect; module ≡-Reasoning)
  renaming ([_] to [_]ⁱ)

import Function.Related as Related

open import Util
open import ExpLang
open import ImpLang
open import LoopUnrolling
open import HomEmb
open import SimpExpAsFOT

--
-- Giving a formal proof of Kruskal's theorem
-- is beyond the scope of the current work,
-- so we just postulate it.
--

postulate
  Kruskal : {V F : Set} (s : Sequence (FOTerm V F)) →
    ∃₂ λ (i j : ℕ) → i < j × (s i ⊴ s j)

-- TODO: a formal proof of `firstEmbedded-total` from `Kruskal`.

postulate
  firstEmbedded-total :
    (s : Sequence (FOTerm ⊥ TrmCons))→
      ∃₂ λ n m → firstEmbedded n s ≡ just m

--
-- A basic supercompiler
--

-- It first builds a stream of iterated unrollings of the program in KNF.
-- Then it looks for pairs of initializer expressions related by homeomorphic
-- embedding in an initial fragment of the stream (the length of this fragment
-- being specified by an input parameter -- `n`).

-- We use only initializer expressions when checking for termination,
-- because they are the only KNF part changed by the simple loop unrolling
-- used here.

-- To aid the experimentations on practical examples, there is also an input
-- option, `alwaysJust`, which can be used to force a result even if
-- no homeomorphic embedding is found in the specified initial stream segment.

--
-- Whistle
--

-- knfs⇒FOTerms

knfs⇒FOTerms : (knfs : Sequence KNFProg) → Sequence (FOTerm ⊥ TrmCons)

knfs⇒FOTerms knfs = TrmToFOTerm ∘ initExp ∘ knfs

-- whistle

whistle :
  (alwaysJust : Bool) → (n : ℕ) → (knfs : Sequence KNFProg) →
    Maybe ℕ

whistle alwaysJust n knfs =
  maybe′ just (if alwaysJust then just n else nothing)
         (firstEmbedded n (knfs⇒FOTerms knfs))

-- whistle-total

whistle-total :
  ∀ (b : Bool) (knfs : Sequence KNFProg)→
    ∃₂ λ n m → whistle b n knfs ≡ just m

whistle-total b knfs with firstEmbedded-total (knfs⇒FOTerms knfs)
... | n , m , ≡m = n , m ,
  cong (maybe just (if b then just n else nothing)) ≡m

--
-- The main loop of supercompilation
--

-- sscpCore

sscpCore :
  (alwaysJust : Bool) (unroll : KNFProg → KNFProg)
  (n : ℕ) (knf : KNFProg) → Maybe KNFProg

sscpCore alwaysJust unroll n knf =
  maybe′ (just ∘′  knfs) nothing (whistle alwaysJust n knfs)
  where
    knfs = fold knf unroll

-- sscp

sscp : (alwaysJust : Bool) (n : ℕ) (knf : KNFProg) → Maybe KNFProg

sscp alwaysJust n knf = 
  sscpCore alwaysJust unrollToInit n knf


-- Alternatively, we define a cut-down version, which uses `normConv`
-- instead of `norm` during loop unrolling.
-- In essence, it is a simple deforestation analog of the above supercompiler.

-- unrollToInit'

unrollToInit′ : KNFProg → KNFProg

unrollToInit′ (KNF init cond body final) =
  KNF newInit cond body final
  where
    nrm = λ (t : Trm) → ntrm2trm (normConv t)
    newInit = nrm ((IfNil cond Id body) $$ init)

-- sscp′

sscp′ : (alwaysJust : Bool) (n : ℕ) (knf : KNFProg) → Maybe KNFProg

sscp′ alwaysJust n knf = 
  sscpCore alwaysJust unrollToInit′ n knf

--------------------------------------------
-- Proof of Correctness
-- (Totality and preservation of semantics)
--------------------------------------------

-- Totality is a direct consequence of totality of `firstEmbedded`.

-- sscpCore-total

sscpCore-total : ∀ b unroll knf →
  ∃₂ λ (n : ℕ) (knf′ : KNFProg) →
    sscpCore b unroll n knf ≡ just knf′

sscpCore-total b unroll knf =
  helper (whistle-total b knfs)
  where
  knfs = fold knf unroll
  helper : ∃₂ (λ n m → whistle b n knfs ≡ just m) →
           ∃₂ (λ (n : ℕ) (knf′ : KNFProg) →
             sscpCore b unroll n knf ≡ just knf′)
  helper (n , m , ≡m) = n , knfs m , helper≡
    where
    open ≡-Reasoning
    helper≡ = begin
      sscpCore b unroll n knf
        ≡⟨ refl ⟩
      maybe′ (just ∘′  knfs) nothing (whistle b n knfs)
        ≡⟨ cong (maybe′ (just ∘′ knfs) nothing) ≡m ⟩
      maybe′ (just ∘′  knfs) nothing (just m)
        ≡⟨ refl ⟩
      just (knfs m)
      ∎  

-- sscp-total

sscp-total : ∀ b knf →
  ∃₂ λ n knf′ → sscp b n knf ≡ just knf′

sscp-total b knf with sscpCore-total b unrollToInit knf
... | n , knf′ , ≡knf′ = n , knf′ , ≡knf′


-- Preservation of semantics is established through a sequence of lemmas,
-- relying only on correctness of one-step loop unrolling.

-- PreservesCond

PreservesCond : (KNFProg → KNFProg) → Set
PreservesCond unroll = ∀ knf → condExp (unroll knf) ≡ condExp knf

-- unrolling-preserves-condExp

unrolling-preserves-condExp :
  ∀ {unroll} → PreservesCond unroll →
  ∀ {knf} n → condExp (fold knf unroll n) ≡ condExp knf

unrolling-preserves-condExp pu zero = refl

unrolling-preserves-condExp {unroll} unroll≡ {knf} (suc n) = begin
  condExp (unroll (fold knf unroll n))
    ≡⟨ unroll≡ (fold knf unroll n) ⟩
  condExp (fold knf unroll n)
    ≡⟨ unrolling-preserves-condExp unroll≡  n ⟩
  condExp knf
  ∎
  where open ≡-Reasoning

-- unrolling-preserves-Pcond

unrolling-preserves-Pcond :
  ∀ {knf unroll} n →
  PreservesCond unroll →
  ∀ {p} (P : Trm → Set p) →
  P (condExp knf) →
  P (condExp (fold knf unroll n))

unrolling-preserves-Pcond  {knf} {unroll} n unroll≡ P =
  P (condExp knf)
    ∼⟨ subst P (P.sym $ unrolling-preserves-condExp unroll≡ n) ⟩
  P (condExp (fold knf unroll n))
  ∎
  where open Related.EquationalReasoning

-- ⊨KNF-unrolling

⊨KNF-unrolling :
  ∀ {knf unroll v v′} n →
  PreservesCond unroll →
  StrictKNF knf →
  ⊨KNF-unroller unroll →
  (knf ⊨KNF v ⇓ v′) ⇔
  (fold knf unroll n ⊨KNF v ⇓ v′)

⊨KNF-unrolling zero pcond hs hu =
  Equiv.id

⊨KNF-unrolling  {knf} {unroll} {v} {v′} (suc n) pcond hs hu =
  knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF-unrolling n pcond hs hu ⟩
  fold knf unroll n ⊨KNF v ⇓ v′
    ∼⟨ hu (unrolling-preserves-Pcond n pcond StrictTrm hs) ⟩
  unroll (fold knf unroll n) ⊨KNF v ⇓ v′
    ≡⟨ cong (λ z → z ⊨KNF v ⇓ v′) refl ⟩
  fold knf unroll (suc n) ⊨KNF v ⇓ v′
  ∎
  where open Related.EquationalReasoning

-- evalKNF-unrolling

evalKNF-unrolling :
  ∀ knf unroll v v′ n →
  PreservesCond unroll →
  StrictKNF knf →
  ⊨KNF-unroller unroll →
  (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
  (∃ λ (i′ : ℕ) → evalKNF i′ (fold knf unroll n) v ≡ just v′)

evalKNF-unrolling knf unroll v v′ n pcond hs hu =
  (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′)
    ∼⟨ sym $ ⊨KNF⇔evalKNF ⟩
  knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF-unrolling n pcond hs hu ⟩
  fold knf unroll n ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF⇔evalKNF ⟩
  (∃ λ (i′ : ℕ) → evalKNF i′ (fold knf unroll n) v ≡ just v′)
  ∎
  where open Related.EquationalReasoning

-- sscpCore-is-fold

sscpCore-is-fold :
  ∀ unroll b n knf knf′ →
    sscpCore b unroll n knf ≡ just knf′ →
    ∃ λ m → knf′ ≡ fold knf unroll m

sscpCore-is-fold unroll b n knf knf′ ≡knf′
  with whistle b n (fold knf unroll)

sscpCore-is-fold unroll b n knf knf′ ≡knf′ | just m =
  m , just-injective (P.sym ≡knf′)

sscpCore-is-fold unroll b n knf knf′ () | nothing

-- sscpCore-correct

sscpCore-correct :
  ∀ unroll b knf knf′ v v′ n →
    PreservesCond unroll →
    StrictKNF knf →
    ⊨KNF-unroller unroll →
    sscpCore b unroll n knf ≡ just knf′ →
      (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
      (∃ λ (i′ : ℕ) → evalKNF i′ knf′  v ≡ just v′)

sscpCore-correct unroll b knf knf′ v v′ n pcond hs hu hc
  with sscpCore-is-fold unroll b n knf knf′ hc
... | m , ≡unfold =
    (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′)
      ∼⟨ evalKNF-unrolling knf unroll v v′ m pcond hs hu ⟩
    (∃ λ (i′ : ℕ) → evalKNF i′ (fold knf unroll m) v ≡ just v′)
      ≡⟨ cong (λ z → ∃ (λ (i′ : ℕ) → evalKNF i′ z v ≡ just v′))
              (P.sym $ ≡unfold) ⟩
    (∃ λ (i′ : ℕ) → evalKNF i′ knf′ v ≡ just v′)
    ∎
    where open Related.EquationalReasoning

-- sscp-correct

sscp-correct :
  ∀ b knf knf′ n v v′ → 
    StrictKNF knf →
    sscp b n knf ≡ just knf′ →
      (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
      (∃ λ (i′ : ℕ) → evalKNF i′ knf′  v ≡ just v′)

sscp-correct b knf knf′ n v v′ hs hc =
  sscpCore-correct unrollToInit b knf knf′ v v′ n
                   (λ knf' → refl) hs unrollToInit-is-⊨KNF-unroller hc

--
