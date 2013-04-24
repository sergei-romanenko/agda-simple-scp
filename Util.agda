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

open ≡-Reasoning
open Membership-≡

-- ++-[]

++-[] : ∀ {ℓ} {A : Set ℓ} (xs : List A) →
  xs ++ [] ≡ xs
++-[] [] = refl
++-[] (x ∷ xs) = cong (_∷_ x) (++-[] xs)

-- ++-assoc

++-assoc : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) →
  (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

-- foldl⇒foldr

foldl⇒foldr : ∀ {A B : Set} (f : B → A → B) → ∀ n xs →
                foldl f n xs ≡ foldr (λ b g x → g (f x b)) id xs n
foldl⇒foldr f n [] = refl
foldl⇒foldr f n (b ∷ xs) =
  begin
    foldl f (f n b) xs
      ≡⟨ foldl⇒foldr f (f n b) xs ⟩
    foldr (λ b g x → g (f x b)) id xs (f n b)
      ≡⟨ refl ⟩
    foldr (λ b g x → g (f x b)) id (b ∷ xs) n
  ∎


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

foldr-∷ʳ : ∀ {A B : Set} (f : A → B → B) → ∀ n xs x →
          foldr f n (xs ∷ʳ x) ≡ foldr f (f x n) xs
foldr-∷ʳ f n [] x = refl
foldr-∷ʳ f n (x' ∷ xs) x = cong (f x') (foldr-∷ʳ f n xs x)

-- foldl⇒foldr-reverse

foldl⇒foldr-reverse :
  ∀ {A B : Set} (f : B → A → B) → ∀ n xs →
    foldl f n xs ≡ foldr (flip f) n (reverse xs)
foldl⇒foldr-reverse f n [] = refl
foldl⇒foldr-reverse f n (x ∷ xs) =
  begin
    foldl f n (x ∷ xs)
      ≡⟨ refl ⟩
    foldl f (f n x) xs
      ≡⟨ foldl⇒foldr-reverse f (f n x) xs ⟩
    foldr (flip f) ((flip f) x n) (reverse xs)
      ≡⟨ sym (foldr-∷ʳ (flip f) n (reverse xs) x) ⟩
    foldr (flip f) n (reverse xs ++ [ x ])
      ≡⟨ cong (foldr (flip f) n) (sym (unfold-reverse x xs)) ⟩
    foldr (flip f) n (reverse (x ∷ xs))
  ∎

--
-- Sequences
--

-- The word `Sequence` is used to avoid conflict with `stream`
-- (in Data.Stream).

Sequence : Set → Set
Sequence A = ℕ → A

ℕ-seq : (k l : ℕ) → List ℕ
ℕ-seq k zero = []
ℕ-seq k (suc l) = k ∷ ℕ-seq (suc k) l

find-in-list : ∀ {a} {A : Set a} (p : A → Bool) → List A → Maybe A
find-in-list p [] = nothing
find-in-list p (x ∷ xs) with p x
... | true = just x
... | false = find-in-list p xs

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

<⇒≤ : {m n : ℕ} → m < n → m ≤ n
<⇒≤ (s≤s z≤n) = z≤n
<⇒≤ (s≤s (s≤s m≤n)) = s≤s (<⇒≤ (s≤s m≤n))

--
