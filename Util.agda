module Util where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Data.Unit using (⊤)

open import Data.List.Properties
open import Data.List.Any
  using (here; there; module Membership-≡)
open import Data.List.Reverse

import Level
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]ⁱ)


import Algebra
module LM {a} {A : Set a} = Algebra.Monoid (Data.List.monoid A)

open ≡-Reasoning
open Membership-≡

-- reverse-involutive

reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
      ≡⟨ cong reverse (unfold-reverse x xs) ⟩
    reverse (reverse xs ++ [ x ])
      ≡⟨ refl ⟩
    reverse (reverse xs ++ reverse [ x ])
      ≡⟨ reverse-++-commute (reverse xs) [ x ] ⟩
    reverse (reverse [ x ]) ++ reverse (reverse xs)
      ≡⟨ cong (_∷_ x) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎

-- foldr-∷ʳ

foldr-∷ʳ : ∀ {A B : Set} (f : A → B → B) → ∀ {n x} xs →
          foldr f n (xs ∷ʳ x) ≡ foldr f (f x n) xs
foldr-∷ʳ f [] = refl
foldr-∷ʳ f (y ∷ xs) = cong (f y) (foldr-∷ʳ f xs)

-- foldr∘reverse

foldr∘reverse :
  ∀ {A B : Set} (f : A → B → B) → ∀ n xs →
    foldr f n (reverse xs) ≡ foldl (flip f) n xs

foldr∘reverse f n [] =
  refl

foldr∘reverse f n (x ∷ xs) = begin
  foldr f n (reverse (x ∷ xs))
    ≡⟨ cong (foldr f n) (unfold-reverse x xs) ⟩
  foldr f n (reverse xs ++ [ x ])
    ≡⟨ foldr-∷ʳ f (reverse xs) ⟩
  foldr f (f x n) (reverse xs)
    ≡⟨ foldr∘reverse f (f x n) xs ⟩
  foldl (flip f) n (x ∷ xs)
  ∎

--
-- Sequences
--

-- The word `Sequence` is used to avoid conflict with `stream`
-- (in Data.Stream).

-- Sequence

Sequence : Set → Set
Sequence A = ℕ → A

-- ℕ-seq

ℕ-seq : (k l : ℕ) → List ℕ

ℕ-seq k zero = []
ℕ-seq k (suc l) = k ∷ ℕ-seq (suc k) l

-- find-in-list

find-in-list : ∀ {a} {A : Set a} (p : A → Bool) → List A → Maybe A

find-in-list p [] = nothing
find-in-list p (x ∷ xs) with p x
... | true = just x
... | false = find-in-list p xs

-- find-just

find-just : ∀ {a} {A : Set a}
  (p : A → Bool) (x : A) (xs : List A) →
  x ∈ xs → p x ≡ true →
  ∃ λ y → find-in-list p xs ≡ just y

find-just p x [] () px≡true

find-just p x (y ∷ xs) (here x≡y) px≡true
  rewrite sym x≡y | px≡true = x , refl
find-just p x (y ∷ xs) (there pxs) px≡true with p y
... | true = y , refl
... | false with find-in-list p xs | find-just p x xs
find-just p x (y ∷ xs) (there pxs) px≡true
  | false | just z | h = z , refl
find-just p x (y ∷ xs) (there pxs) px≡true
  | false | nothing | h = h pxs px≡true

-- just-injective

just-injective : ∀ {ℓ} {A : Set ℓ} {x y : A} →
  (just x ∶ Maybe A) ≡ just y → x ≡ y
just-injective refl = refl

-- maybe-dec

maybe-dec : ∀ {ℓ} {A : Set ℓ}
  (_≟A_ : (x y : A) → Dec (x ≡ y)) →
  {u v : Maybe A} → Dec (u ≡ v)

maybe-dec _≟A_ {just x} {just y} with x ≟A y
... | yes x≡y = yes (cong just x≡y)
... | no  x≢y = no (x≢y ∘ just-injective)

maybe-dec _≟A_ {just x} {nothing} =
  no (λ ())

maybe-dec _≟A_ {nothing} {just x} =
  no (λ ())

maybe-dec _≟A_ {nothing} {nothing} =
  yes refl

-- <⇒≤

<⇒≤ : {m n : ℕ} → m < n → m ≤ n
<⇒≤ (s≤s z≤n) = z≤n
<⇒≤ (s≤s (s≤s m≤n)) = s≤s (<⇒≤ (s≤s m≤n))

--
