module Examples where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import ExpLang

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


--