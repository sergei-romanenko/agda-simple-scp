module Examples where

open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import ExpLang
open import PositiveInfo
open import ImpLang

norm₁ :
  ntrm2trm (normConv ((IfNil Hd (Tl $$ Tl ∷ Hd $$ Tl) Tl) $$ ([] ∷ Id)))
  ≡ Tl ∷ Hd
norm₁ = refl


replaceAt₁ :
  ntrm2trm (replaceAt (HD ∷ []) (normConv Id) (normConv ([] ∷ [])))
  ≡ ([] ∷ []) ∷ Tl
replaceAt₁ = refl

module replaceAt₂ where
  nt1 = normConv (IfNil Hd (Hd $$ Tl) (Tl $$ Tl))
  nt2 = normConv (Tl $$ Hd $$ Tl ∷ Hd $$ Hd $$ Tl)
  prop : ntrm2trm (normNCmp nt1 (replaceAt (TL ∷ HD ∷ [])
                            (normConv Id) nt2))
         ≡ IfNil Hd (Tl $$ Hd $$ Tl ∷ Hd $$ Hd $$ Tl) (Tl $$ Tl)
  prop = refl

pos-info-prop₁ :
  ntrm2trm (norm (IfNil Hd ([] ∷ []) (IfNil Hd [] Tl)))
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
listToVal vs = foldr VCons VNil vs

evalKNF₁ :
  evalKNF 3 revList-knf (listToVal (VNil ∷ (VCons VNil VNil) ∷ []))
  ≡
  just (VCons (VCons VNil VNil) (VCons VNil VNil))
evalKNF₁ = refl

--
