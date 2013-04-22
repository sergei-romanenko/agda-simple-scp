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

open import Function
open import Function.Equality
  using (_⟨$⟩_; module Π)
open import Function.Equivalence as Equiv
  using (module Equivalence; _⇔_; equivalence)

open import Relation.Nullary
open import Relation.Nullary.Decidable
  using (⌊_⌋)

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong; subst; inspect; module ≡-Reasoning)
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

-- sscpCore

sscpCore :
  (alwaysJust : Bool) (unroll : KNFProg → KNFProg)
  (n : ℕ) (knf : KNFProg) → Maybe KNFProg

sscpCoreRet :
  (alwaysJust : Bool) → (n : ℕ) → (knfs : Sequence KNFProg) → Maybe ℕ →
  Maybe KNFProg

sscpCore alwaysJust unroll n knf =
  sscpCoreRet alwaysJust n knfs (firstEmbedded n s)
  where
    knfs = sequenceUnfold knf unroll
    s = sequenceMap (λ knf → TrmToFOTerm (initExp knf)) knfs

sscpCoreRet alwaysJust n knfs =
  maybe′ (just ∘′ knfs)
    (if alwaysJust then just (knfs n) else nothing)

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
  helper (firstEmbedded-total s)
  where
  knfs = sequenceUnfold knf unroll
  s = sequenceMap (λ knf → TrmToFOTerm (initExp knf)) knfs
  helper : ∃₂ (λ n m → firstEmbedded n s ≡ just m) →
           ∃₂ (λ (n : ℕ) (knf′ : KNFProg) →
             sscpCore b unroll n knf ≡ just knf′)
  helper (n , m , ≡m) = n , knfs m , helper≡
    where
    open ≡-Reasoning
    helper≡ = begin
      sscpCore b unroll n knf
        ≡⟨ refl ⟩
      sscpCoreRet b n knfs (firstEmbedded n s)
        ≡⟨ cong (sscpCoreRet b n knfs) ≡m ⟩
      sscpCoreRet b n knfs (just m)
        ≡⟨ refl ⟩
      just (sequenceUnfold knf unroll m)
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

-- condExp-unrollToInitSequence

unrolling-preserves-condExp :
  ∀ {knf} n → condExp (sequenceUnfold knf unrollToInit n) ≡ condExp knf

unrolling-preserves-condExp zero =
  refl
unrolling-preserves-condExp (suc n) =
  unrolling-preserves-condExp n

-- unrolling-preserves-Pcond

unrolling-preserves-Pcond :
  ∀ {knf} n {p} (P : Trm → Set p) →
  P (condExp knf) →
  P (condExp (sequenceUnfold knf unrollToInit n))

unrolling-preserves-Pcond {knf} n P =
  P (condExp knf)
    ∼⟨ subst P (P.sym $ unrolling-preserves-condExp n) ⟩
  P (condExp (sequenceUnfold knf unrollToInit n))
  ∎
  where open Related.EquationalReasoning

-- ⊨KNF-unrollToInitSequence

⊨KNF-unrollToInitSequence :
  ∀ {knf v v′} n →
  strictTrm (condExp knf) →
  (knf ⊨KNF v ⇓ v′) ⇔
  (sequenceUnfold knf unrollToInit n ⊨KNF v ⇓ v′)

⊨KNF-unrollToInitSequence zero hs =
  Equiv.id

⊨KNF-unrollToInitSequence {knf} {v} {v′} (suc n) hs =
  knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF-unrollToInitSequence n hs ⟩
  sequenceUnfold knf unrollToInit n ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF-unrollToInit ( unrolling-preserves-Pcond n strictTrm hs) ⟩
  unrollToInit (sequenceUnfold knf unrollToInit n) ⊨KNF v ⇓ v′
    ≡⟨ cong (λ z → z ⊨KNF v ⇓ v′) refl ⟩
  sequenceUnfold knf unrollToInit (suc n) ⊨KNF v ⇓ v′
  ∎
  where open Related.EquationalReasoning

-- evalKNF-unrollToInitSequence

evalKNF-unrollToInitSequence :
  ∀ knf v v′ n →
  strictTrm (condExp knf) →
  (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
  (∃ λ (i′ : ℕ) → evalKNF i′ (sequenceUnfold knf unrollToInit n) v ≡ just v′)

evalKNF-unrollToInitSequence knf v v′ n  hs =
  (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′)
    ∼⟨ sym $ ⊨KNF⇔evalKNF ⟩
  knf ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF-unrollToInitSequence n hs ⟩
  sequenceUnfold knf unrollToInit n ⊨KNF v ⇓ v′
    ∼⟨ ⊨KNF⇔evalKNF ⟩
  (∃ λ (i′ : ℕ) → evalKNF i′ (sequenceUnfold knf unrollToInit n) v ≡ just v′)
  ∎
  where open Related.EquationalReasoning


{-
⊨-sscpCore-correct :
  ∀ b knf knf′ n v v′ →
    strictTrm (condExp knf) →
    sscpCore b unrollToInit n knf ≡ just knf′ →
      (knf ⊨KNF v ⇓ v′) ⇔
      (knf′ ⊨KNF  v ⇓ v′)

⊨-sscpCore-correct b knf knf′ n v v′ hs ≡knf′ =
  helper (firstEmbedded n s)
  where
  open Related.EquationalReasoning

  knfs = sequenceUnfold knf unrollToInit
  s = sequenceMap (λ knf → TrmToFOTerm (initExp knf)) knfs

  helper : Maybe ℕ → (knf ⊨KNF v ⇓ v′) ⇔ (knf′ ⊨KNF v ⇓ v′)
  helper (just m) = {!!}
  helper nothing = {!!}
{-
  knf ⊨KNF v ⇓ v′
    ∼⟨ {!!} ⟩
  knf′ ⊨KNF v ⇓ v′
    ∎
-}
-}

{-
sscpCore-correct :
  ∀ b knf knf′ n v v′ →
    strictTrm (condExp knf) →
    sscpCore b unrollToInit n knf ≡ just knf′ →
      (∃ λ (i : ℕ) → evalKNF i knf v ≡ just v′) ⇔
      (∃ λ (i′ : ℕ) → evalKNF i′ knf′  v ≡ just v′)

sscpCore-correct b knf knf′ n v v′ hs hc = {!!}
-}



--
