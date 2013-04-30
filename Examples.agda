module Examples where

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Function

open import ExpLang
open import PositiveInfo
open import ImpLang
open import LoopUnrollingScp

norm₁ :
  ⌈ ⌋ (IfNil Hd (Tl $$ Tl ∷ Hd $$ Tl) Tl) $$ ([] ∷ Id) ⌊ ⌉
  ≡ Tl ∷ Hd
norm₁ = refl


replaceAt₁ :
  ⌈  replaceAt (HD ∷ []) (⌋ Id ⌊) (⌋ [] ∷ [] ⌊) ⌉
  ≡ ([] ∷ []) ∷ Tl
replaceAt₁ = refl

module replaceAt₂ where
  nt1 = ⌋ IfNil Hd (Hd $$ Tl) (Tl $$ Tl) ⌊
  nt2 = ⌋ Tl $$ Hd $$ Tl ∷ Hd $$ Hd $$ Tl ⌊
  prop : ⌈ nt1 ○ (replaceAt (TL ∷ HD ∷ []) (⌋ Id ⌊) nt2) ⌉
         ≡ IfNil Hd (Tl $$ Hd $$ Tl ∷ Hd $$ Hd $$ Tl) (Tl $$ Tl)
  prop = refl

pos-info-prop₁ :
  ⌈ norm (IfNil Hd ([] ∷ []) (IfNil Hd [] Tl)) ⌉
  ≡ IfNil Hd ([] ∷ []) Tl
pos-info-prop₁ = refl

revList-knf : KNFProg
revList-knf = KNF (Id ∷ []) Hd (Tl $$ Hd ∷ Hd $$ Hd ∷ Tl) Tl

revList-prog : KNFtoProg revList-knf ≡
  var≔ Id ∷ [] //
  while[ Hd ]
       var≔ Tl $$ Hd ∷ Hd $$ Hd ∷ Tl //
  var≔ Tl
revList-prog = refl

listToVal : List Val → Val
listToVal vs = foldr _∷ˣ_ []ˣ vs

evalKNF₁ :
  evalKNF 3 revList-knf (listToVal ([]ˣ ∷ ([]ˣ ∷ˣ []ˣ) ∷ []))
  ≡
  just (([]ˣ ∷ˣ []ˣ) ∷ˣ ([]ˣ ∷ˣ []ˣ))
evalKNF₁ = refl

--
-- Examples of supercompilation
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
-- If it is []ˣ, we make the list empty to force an exit of the loop,
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
