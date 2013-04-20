--
-- Simple supercompiler using loop unrolling
--

module LoopUnrollingScp where

open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Product

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

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

sscpCore alwaysJust unroll n knf =
  helper (firstEmbedded n ts) alwaysJust
  where
    knfs = sequenceUnfold knf unroll
    ts = sequenceMap (λ knf → TrmToFOTerm (initExp knf)) knfs

    helper : Maybe ℕ → Bool → Maybe KNFProg
    helper (just m) aj = just (knfs m)
    helper nothing true = just (knfs n)
    helper nothing false = nothing    

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

--
-- Examples
--

-- The task of checking if an input list of booleans contains
-- at least one false value can be performed by the following program.

listHasWFalse-knf = 
  KNF (Id ∷ WFalse) Hd (IfNil (Hd $$ Hd) ([] ∷ WTrue) ((Tl $$ Hd) ∷ Tl)) Tl
  where WFalse = []; WTrue  = [] ∷ []

listHasWFalse-knf-prog :
  KNFtoProg listHasWFalse-knf ≡
    var≔ Id ∷ [] //
    while[ Hd ]
      (var≔ IfNil (Hd $$ Hd) ([] ∷ [] ∷ []) (Tl $$ Hd ∷ Tl)) //
    var≔ Tl

listHasWFalse-knf-prog = refl

-- We extend the computation state with a flag to hold the final result -
-- at position Tl - while keeping the original input list at position Hd.
-- Then we loop while the list is not empty, and test its head.
-- If it is VNil, we make the list empty to force an exit of the loop,
-- and set the result to true, otherwise we remove the list head and continue.

-- Next, we introduce a specialized version of this program, which,
-- if the input list is not empty, adds a negated copy of the head of the list.
-- The idea is clearly that this specialized version should return true on all
-- non-empty lists, and false only on the empty list.

modifyKNFinput : KNFProg → Trm → KNFProg

modifyKNFinput (KNF init cond body final) modifierExp =
  KNF (init $$ modifierExp) cond body final

listHasWFalse-knf-negdupHd = 
  modifyKNFinput listHasWFalse-knf (IfNil Id Id (negate Hd ∷ Id))
  where WFalse = []; WTrue = [] ∷ []
        negate = λ x → IfNil x WTrue WFalse

maybe-KNFtoProg : Maybe KNFProg → Maybe Stmt

maybe-KNFtoProg = maybe′ (just ∘′  KNFtoProg) nothing

listHasWFalse-knf-negdupHd-scp :
   maybe-KNFtoProg (sscp false 3 listHasWFalse-knf-negdupHd)
  ≡ just (
    var≔ IfNil Id ([] ∷ [])
               (IfNil (Hd) ([] ∷ [] ∷ []) ([] ∷ [] ∷ [])) //
    while[ Hd ]
      var≔ IfNil (Hd $$ Hd) ([] ∷ [] ∷ []) (Tl $$ Hd ∷ Tl) //
    var≔ Tl)

listHasWFalse-knf-negdupHd-scp = refl

-- While the resulting program may not look simplified at first,
-- if we remove by hand the second if-expression with equal branches,
-- we can see that the loop will never be entered.

{-

    var≔ IfNil Id ([] ∷ []) ([] ∷ [] ∷ []) //
    while[ Hd ]
      var≔ IfNil (Hd $$ Hd) ([] ∷ [] ∷ []) (Tl $$ Hd ∷ Tl) //
    var≔ Tl

-}

-- The final correct result will be computed directly by the initializer
-- expression.
-- The combination of deforestation, positive information propagation and
-- simple loop unrolling has resulted in an almost optimal specialized program.

-- In contrast, if we remove just positive information propagation
-- from the mix, the end result is much less satisfactory:

listHasWFalse-knf-negdupHd-scp′ :
   maybe-KNFtoProg (sscp′ false 3 listHasWFalse-knf-negdupHd)
  ≡ just (
    var≔
      IfNil Id
            (IfNil Id
              (IfNil Id Id (IfNil Hd ([] ∷ []) [] ∷ Id) ∷ [])
              (IfNil Id
                (IfNil Hd ([] ∷ [] ∷ []) (IfNil Id Tl Id ∷ []))
                (IfNil Hd (IfNil Id Tl Id ∷ []) ([] ∷ [] ∷ []))))
            (IfNil Id
              (IfNil Hd ([] ∷ [] ∷ []) (IfNil Id Tl Id ∷ []))
              (IfNil Hd (IfNil Id Tl Id ∷ []) ([] ∷ [] ∷ []))) //
    while[ Hd ]
      var≔ IfNil (Hd $$ Hd) ([] ∷ [] ∷ []) (Tl $$ Hd ∷ Tl) //
    var≔ Tl)

listHasWFalse-knf-negdupHd-scp′ = refl

--
