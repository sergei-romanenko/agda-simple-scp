module Examples where

open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import ExpLang
open import PositiveInfo
open import ImpLang

infixr 6 _$$_
infixr 5 _#_

_$$_ : ∀ (x y : Trm) → Trm
x $$ y = Cmp x y

_#_ : ∀ (h t : Trm) → Trm
h # t = Cons h t

Hd = Sel HD
Tl = Sel TL

norm₁ :
  ntrm2trm (normConv ((IfNil Hd ((Tl $$ Tl) # (Hd $$ Tl)) Tl) $$ (Nil # Id)))
  ≡ Tl # Hd
norm₁ = refl


replaceAt₁ :
  ntrm2trm (replaceAt (HD ∷ []) (normConv Id) (normConv (Nil # Nil)))
  ≡ (Nil # Nil) # Tl
replaceAt₁ = refl

module replaceAt₂ where
  nt1 = normConv (IfNil Hd (Hd $$ Tl) (Tl $$ Tl))
  nt2 = normConv (Tl $$ Hd $$ Tl # Hd $$ Hd $$ Tl)
  prop : ntrm2trm (normNCmp nt1 (replaceAt (TL ∷ HD ∷ [])
                            (normConv Id) nt2))
         ≡ IfNil Hd (Tl $$ Hd $$ Tl # Hd $$ Hd $$ Tl) (Tl $$ Tl)
  prop = refl

pos-info-prop₁ :
  ntrm2trm (norm (IfNil Hd (Nil # Nil) (IfNil Hd Nil Tl)))
  ≡ IfNil Hd (Nil # Nil) Tl
pos-info-prop₁ = refl

revList-knf : KNFProg
revList-knf = KNF (Id # Nil) Hd (Tl $$ Hd # Hd $$ Hd # Tl) Tl

revList-prog : KNFtoProg revList-knf ≡
  Seq (Assign (Cons Id Nil))
      (Seq (While (Sel HD)
                  (Assign (Cons (Cmp (Sel TL) (Sel HD))
                                (Cons (Cmp (Sel HD) (Sel HD)) (Sel TL)))))
           (Assign (Sel TL)))
revList-prog = refl

listToVal : List Val → Val
listToVal vs = foldr VCons VNil vs

evalKNF₁ :
  evalKNF 3 revList-knf (listToVal (VNil ∷ (VCons VNil VNil) ∷ []))
  ≡
  just (VCons (VCons VNil VNil) (VCons VNil VNil))
evalKNF₁ = refl

--
