module PositiveInfo where

open import Data.List
open import Data.Empty
open import Data.Unit

open import Relation.Binary.PropositionalEquality
  renaming([_] to [_]ⁱ)

open import Function
open ≡-Reasoning

open import Util
open import ExpLang

-- We can propagate information about the results of test
-- inside the branches of a conditional expressions.
-- This transformation is one of the key differences that distinguish
-- supercompilation from weaker optimizations like classical
-- partial evaluation and deforestation.

-- Basically, the idea is that a term t can be replaced either
-- with []ⁿ or (t !ⁿ HD ∷ⁿ t !ⁿ TL), so that some additional simplifications
-- become possible.
-- However, transformations of that kind are correct only under certain
-- conditions.

-- Replacing a subterm with []ⁿ .

-- [_]≔[]ⁿ

[_]≔[]ⁿ : (sels : List Selector) → NTrm

[ sels ]≔[]ⁿ =
  ⟪ [] ⟫ⁿ [ sels ]≔ⁿ []ⁿ

-- Replacing a subterm with ∷ⁿ .

-- [_]≔∷ⁿ

[_]≔∷ⁿ : (sels : List Selector) → NTrm

[ sels ]≔∷ⁿ = 
  ⟪ [] ⟫ⁿ [ sels ]≔ⁿ (⟪ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels ++ [ TL ] ⟫ⁿ)

-- To prove the correctness of positive information propagation
-- we will need a number of (conceptually simple) lemmas.
-- Proving them is a tedious work, though...

-- []≔[]ⁿ∘○⟪⟫ⁿ

[]≔[]ⁿ∘○⟪⟫ⁿ : (sels1 sels2 : List Selector) →
  [ sels1 ]≔[]ⁿ ○⟪ sels2 ⟫ⁿ
    ≡ ⟪ sels2 ⟫ⁿ [ sels1 ]≔ⁿ []ⁿ

[]≔[]ⁿ∘○⟪⟫ⁿ [] sels2 = refl

[]≔[]ⁿ∘○⟪⟫ⁿ (HD ∷ sels1) sels2 =
  begin
    ([ HD ∷ sels1 ]≔[]ⁿ ○⟪ sels2 ⟫ⁿ)
      ≡⟨ refl ⟩
    (⟪ [ HD ] ⟫ⁿ [ sels1 ]≔ⁿ []ⁿ ○⟪ sels2 ⟫ⁿ) ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ cong₂ _∷ⁿ_ (cong₂ _○⟪_⟫ⁿ (sym $ []≔[]ⁿ∘○⟪⟫ⁿ sels1 [ HD ]) refl) refl ⟩
    ([ sels1 ]≔[]ⁿ ○⟪ [ HD ] ⟫ⁿ ○⟪ sels2 ⟫ⁿ) ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ cong₂ _∷ⁿ_ (sym $ ○⟪⟫ⁿ∘++ [ sels1 ]≔[]ⁿ sels2 [ HD ]) refl ⟩
    ([ sels1 ]≔[]ⁿ ○⟪ sels2 ++ [ HD ] ⟫ⁿ) ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ cong₂ _∷ⁿ_ ([]≔[]ⁿ∘○⟪⟫ⁿ sels1 (sels2 ++ [ HD ])) refl ⟩
    ⟪ sels2 ++ [ HD ] ⟫ⁿ [ sels1 ]≔ⁿ []ⁿ ∷ⁿ ⟪ sels2 ++ [ TL ] ⟫ⁿ
      ≡⟨ refl ⟩
    ⟪ sels2 ⟫ⁿ [ HD ∷ sels1 ]≔ⁿ []ⁿ
  ∎

[]≔[]ⁿ∘○⟪⟫ⁿ (TL ∷ sels1) sels2
  rewrite sym $ []≔[]ⁿ∘○⟪⟫ⁿ sels1 [ TL ]
        | sym $ ○⟪⟫ⁿ∘++ ([ sels1 ]≔[]ⁿ) sels2 [ TL ]
        | []≔[]ⁿ∘○⟪⟫ⁿ sels1 (sels2 ++ [ TL ])
  = refl

-- []≔∷ⁿ∘○⟪⟫ⁿ

[]≔∷ⁿ∘○⟪⟫ⁿ : (sels1 sels2 : List Selector) →
  [ sels1 ]≔∷ⁿ ○⟪ sels2 ⟫ⁿ 
  ≡
  ⟪ sels2 ⟫ⁿ [ sels1 ]≔ⁿ
    (⟪ sels2 ++ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ sels2 ++ sels1 ++ [ TL ] ⟫ⁿ)

[]≔∷ⁿ∘○⟪⟫ⁿ [] sels2 = refl

[]≔∷ⁿ∘○⟪⟫ⁿ (HD ∷ sels1) sels2
  rewrite sym $ LM.assoc sels2 [ HD ] (sels1 ++ [ HD ])
        | sym $ LM.assoc sels2 [ HD ] (sels1 ++ [ TL ])
  = cong (flip _∷ⁿ_ ⟪ sels2 ++ [ TL ] ⟫ⁿ)
         helper
  where
    helper = begin
      ⟪ [ HD ] ⟫ⁿ [ sels1 ]≔ⁿ
        (⟪ [ HD ] ++ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ
           ⟪ [ HD ] ++ sels1 ++ [ TL ] ⟫ⁿ) ○⟪ sels2 ⟫ⁿ
        ≡⟨ cong (flip _○⟪_⟫ⁿ sels2) (sym $ []≔∷ⁿ∘○⟪⟫ⁿ sels1 [ HD ]) ⟩
      [ sels1 ]≔∷ⁿ ○⟪ [ HD ] ⟫ⁿ ○⟪ sels2 ⟫ⁿ
        ≡⟨ sym $ ○⟪⟫ⁿ∘++ [ sels1 ]≔∷ⁿ sels2 [ HD ] ⟩
      [ sels1 ]≔∷ⁿ ○⟪ (sels2 ++ [ HD ]) ⟫ⁿ
        ≡⟨ []≔∷ⁿ∘○⟪⟫ⁿ sels1 (sels2 ++ [ HD ]) ⟩
      ⟪ sels2 ++ [ HD ] ⟫ⁿ [ sels1 ]≔ⁿ
        (⟪ (sels2 ++ [ HD ]) ++ sels1 ++ [ HD ] ⟫ⁿ ∷ⁿ
           ⟪ (sels2 ++ [ HD ]) ++ sels1 ++ [ TL ] ⟫ⁿ)
      ∎

[]≔∷ⁿ∘○⟪⟫ⁿ (TL ∷ sels1) sels2
  rewrite sym $ LM.assoc sels2 [ TL ] (sels1 ++ [ TL ])
        | sym $ LM.assoc sels2 [ TL ] (sels1 ++ [ HD ])
        | sym $ []≔∷ⁿ∘○⟪⟫ⁿ sels1 [ TL ]
        | sym $ []≔∷ⁿ∘○⟪⟫ⁿ sels1 (sels2 ++ [ TL ])
        | ○⟪⟫ⁿ∘++ [ sels1 ]≔∷ⁿ sels2 [ TL ]
  = refl

-- []≔[]ⁿ∘++

[]≔[]ⁿ∘++ : (v : Val) (sels1 sels2 : List Selector) →
  ⟦⌈ [ sels1 ++ sels2 ]≔[]ⁿ ⌉⟧ v !! sels1
    ≡ ⟦⌈ [ sels2 ]≔[]ⁿ ⌉⟧ (v !! sels1)

[]≔[]ⁿ∘++ v sels1 sels2 = begin
  ⟦⌈ [ sels1 ++ sels2 ]≔[]ⁿ ⌉⟧ v !! sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘!!ⁿ ([ sels1 ++ sels2 ]≔[]ⁿ) sels1 v ⟩
  ⟦⌈ [ (sels1 ++ sels2) ]≔[]ⁿ !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip _!!ⁿ_ sels1)
                  ([]≔ⁿ∘++ sels1 sels2 ⟪ [] ⟫ⁿ []ⁿ)) ⟩
  ⟦⌈ ⟪ [] ⟫ⁿ [ sels1 ]≔ⁿ ((⟪ [] ⟫ⁿ !!ⁿ sels1) [ sels2 ]≔ⁿ []ⁿ) !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (!!ⁿ∘[]≔ⁿ-id sels1 ⟪ [] ⟫ⁿ ((⟪ [] ⟫ⁿ !!ⁿ sels1) [ sels2 ]≔ⁿ []ⁿ)) ⟩
  ⟦⌈ (⟪ [] ⟫ⁿ !!ⁿ sels1) [ sels2 ]≔ⁿ []ⁿ ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong₂ (flip _[_]≔ⁿ_ sels2) (!!ⁿ∘⟪⟫ⁿ [] sels1) refl) ⟩
  ⟦⌈ ⟪ sels1 ⟫ⁿ [ sels2 ]≔ⁿ []ⁿ ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v) (sym $ []≔[]ⁿ∘○⟪⟫ⁿ sels2 sels1) ⟩
  ⟦⌈ [ sels2 ]≔[]ⁿ ○⟪ sels1 ⟫ⁿ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○⟪⟫ⁿ (⟪ [] ⟫ⁿ [ sels2 ]≔ⁿ []ⁿ) sels1 v ⟩
  ⟦⌈ [ sels2 ]≔[]ⁿ ⌉⟧ (v !! sels1)
  ∎

-- []≔∷ⁿ∘++

[]≔∷ⁿ∘++ : (v : Val) (sels1 sels2 : List Selector) →
  ⟦⌈ [ sels1 ++ sels2 ]≔∷ⁿ ⌉⟧ v !! sels1
    ≡ ⟦⌈ [ sels2 ]≔∷ⁿ ⌉⟧ (v !! sels1)

[]≔∷ⁿ∘++ v sels1 sels2 = begin
  ⟦⌈ [ sels1 ++ sels2 ]≔∷ⁿ ⌉⟧ v !! sels1
    ≡⟨ sym $ ⟦⌈⌉⟧∘!!ⁿ [ sels1 ++ sels2 ]≔∷ⁿ sels1 v ⟩
  ⟦⌈ [ sels1 ++ sels2 ]≔∷ⁿ !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (flip _!!ⁿ_ sels1)
                  ([]≔ⁿ∘++ sels1 sels2 ⟪ [] ⟫ⁿ
                    (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                      ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ))) ⟩
  ⟦⌈ ⟪ [] ⟫ⁿ [ sels1 ]≔ⁿ
     ((⟪ [] ⟫ⁿ !!ⁿ sels1) [ sels2 ]≔ⁿ
       (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
         ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ)) !!ⁿ sels1 ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (!!ⁿ∘[]≔ⁿ-id sels1 ⟪ [] ⟫ⁿ
              ((⟪ [] ⟫ⁿ !!ⁿ sels1) [ sels2 ]≔ⁿ
                  (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
                    ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ))) ⟩
  ⟦⌈ (⟪ [] ⟫ⁿ !!ⁿ sels1) [ sels2 ]≔ⁿ
        (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
          ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong₂ (flip _[_]≔ⁿ_ sels2) (!!ⁿ∘⟪⟫ⁿ [] sels1) refl) ⟩
  ⟦⌈ ⟪ sels1 ⟫ⁿ [ sels2 ]≔ⁿ
       (⟪ (sels1 ++ sels2) ++ [ HD ] ⟫ⁿ ∷ⁿ
         ⟪ (sels1 ++ sels2) ++ [ TL ] ⟫ⁿ) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v)
            (cong (_[_]≔ⁿ_ ⟪ sels1 ⟫ⁿ sels2)
                  (cong₂ _∷ⁿ_ (cong ⟪_⟫ⁿ (LM.assoc sels1 sels2 [ HD ]))
                              (cong ⟪_⟫ⁿ (LM.assoc sels1 sels2 [ TL ])))) ⟩
  ⟦⌈ ⟪ sels1 ⟫ⁿ [ sels2 ]≔ⁿ
       (⟪ sels1 ++ sels2 ++ [ HD ] ⟫ⁿ ∷ⁿ
          ⟪ sels1 ++ sels2 ++ [ TL ] ⟫ⁿ) ⌉⟧ v
    ≡⟨ cong (flip ⟦⌈_⌉⟧ v) (sym $ []≔∷ⁿ∘○⟪⟫ⁿ sels2 sels1) ⟩
  ⟦⌈ [ sels2 ]≔∷ⁿ ○⟪ sels1 ⟫ⁿ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○⟪⟫ⁿ [ sels2 ]≔∷ⁿ sels1 v ⟩
  ⟦⌈ [ sels2 ]≔∷ⁿ ⌉⟧ (v !! sels1)
  ∎

-- ⟦⌈⌉⟧∘[]≔[]ⁿ

⟦⌈⌉⟧∘[]≔[]ⁿ : (sels : List Selector) (v : Val) →
  v !! sels ≡ []ˣ → ⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ v ≡ v

⟦⌈⌉⟧∘[]≔[]ⁿ [] []ˣ h = refl

⟦⌈⌉⟧∘[]≔[]ⁿ (sel ∷ sels) []ˣ h
  rewrite ↯ˣ-!! sels
  = ⊥-elim (↯ˣ≢[]ˣ h)

⟦⌈⌉⟧∘[]≔[]ⁿ [] (v1 ∷ˣ v2) h =
  ⊥-elim (∷ˣ≢[]ˣ h)

⟦⌈⌉⟧∘[]≔[]ⁿ (HD ∷ sels) (v1 ∷ˣ v2) h =
  cong (flip _∷ˣ_ v2) helper
  where
  helper = begin
    ⟦⌈ ⟪ [ HD ] ⟫ⁿ [ sels ]≔ⁿ []ⁿ ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              ([]≔ⁿ∘⟪⟫ⁿ sels [ HD ] []ⁿ) ⟩
    ⟦⌈ [ [ HD ] ++ sels ]≔[]ⁿ !!ⁿ [ HD ] ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ [ [ HD ] ++ sels ]≔[]ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ HD ]
      ≡⟨ []≔[]ⁿ∘++ (v1 ∷ˣ v2) [ HD ] sels ⟩
    ⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ (v1 ∷ˣ v2 !! [ HD ])
      ≡⟨ refl ⟩
    ⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ v1
      ≡⟨ ⟦⌈⌉⟧∘[]≔[]ⁿ sels v1 h ⟩
    v1
    ∎

⟦⌈⌉⟧∘[]≔[]ⁿ (TL ∷ sels) (v1 ∷ˣ v2) h =
  cong (_∷ˣ_ v1) helper
  where
  helper = begin
    ⟦⌈ ⟪ [ TL ] ⟫ⁿ [ sels ]≔ⁿ []ⁿ ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              ([]≔ⁿ∘⟪⟫ⁿ sels [ TL ] []ⁿ) ⟩
    ⟦⌈ [ [ TL ] ++ sels ]≔[]ⁿ !!ⁿ [ TL ] ⌉⟧ (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ [ [ TL ] ++ sels ]≔[]ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ TL ]
      ≡⟨ []≔[]ⁿ∘++ (v1 ∷ˣ v2) [ TL ] sels ⟩
    ⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ (v1 ∷ˣ v2 !! [ TL ])
      ≡⟨ refl ⟩
    ⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ v2
      ≡⟨ ⟦⌈⌉⟧∘[]≔[]ⁿ sels v2 h ⟩
    v2
    ∎

⟦⌈⌉⟧∘[]≔[]ⁿ sels ↯ˣ h
  rewrite ↯ˣ-!! sels
  = ⊥-elim (↯ˣ≢[]ˣ h)

-- ⟦⌈⌉⟧∘≔∷ⁿ

⟦⌈⌉⟧∘≔∷ⁿ : (sels : List Selector) (v : Val) {u1 u2 : Val} →
  v !! sels ≡ u1 ∷ˣ u2 → ⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ v ≡ v

⟦⌈⌉⟧∘≔∷ⁿ [] []ˣ h = ⊥-elim (∷ˣ≢[]ˣ (sym h))

⟦⌈⌉⟧∘≔∷ⁿ (sel ∷ sels) []ˣ h
  rewrite ↯ˣ-!! sels
  = ⊥-elim (∷ˣ≢↯ˣ (sym h))

⟦⌈⌉⟧∘≔∷ⁿ [] (v1 ∷ˣ v2) h = refl

⟦⌈⌉⟧∘≔∷ⁿ (HD ∷ sels) (v1 ∷ˣ v2) h =
  cong (flip _∷ˣ_ v2) helper
  where
  helper = begin
    ⟦⌈ ⟪ [ HD ] ⟫ⁿ [ sels ]≔ⁿ
         (⟪ (HD ∷ sels) ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ (HD ∷ sels) ++ [ TL ] ⟫ⁿ) ⌉⟧
       (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              ([]≔ⁿ∘⟪⟫ⁿ sels [ HD ]
                (⟪ HD ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ HD ∷ sels ++ [ TL ] ⟫ⁿ)) ⟩
    ⟦⌈ ⟪ [] ⟫ⁿ [ ([ HD ] ++ sels) ]≔ⁿ
         (⟪ HD ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ HD ∷ sels ++ [ TL ] ⟫ⁿ) !!ⁿ [ HD ] ⌉⟧
       (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ ⟪ [] ⟫ⁿ [ ([ HD ] ++ sels) ]≔ⁿ
         (⟪ HD ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ HD ∷ sels ++ [ TL ] ⟫ⁿ) ⌉⟧
       (v1 ∷ˣ v2) !! [ HD ]
      ≡⟨ refl ⟩
    ⟦⌈ [ [ HD ] ++ sels ]≔∷ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ HD ]
      ≡⟨ []≔∷ⁿ∘++ (v1 ∷ˣ v2) (HD ∷ []) sels ⟩
    ⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ (v1 !! [])
      ≡⟨ refl ⟩
    ⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ v1
      ≡⟨ ⟦⌈⌉⟧∘≔∷ⁿ sels v1 h ⟩
    v1
    ∎

⟦⌈⌉⟧∘≔∷ⁿ (TL ∷ sels) (v1 ∷ˣ v2) h =
  cong (_∷ˣ_ v1) helper
  where
  helper = begin
    ⟦⌈ ⟪ [ TL ] ⟫ⁿ [ sels ]≔ⁿ
         (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ) ⌉⟧
       (v1 ∷ˣ v2)
      ≡⟨ cong (flip ⟦⌈_⌉⟧ (v1 ∷ˣ v2))
              ([]≔ⁿ∘⟪⟫ⁿ sels [ TL ]
                (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ)) ⟩
    ⟦⌈ ⟪ [] ⟫ⁿ [ ([ TL ] ++ sels) ]≔ⁿ
         (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ) !!ⁿ [ TL ] ⌉⟧
       (v1 ∷ˣ v2)
      ≡⟨ refl ⟩
    ⟦⌈ ⟪ [] ⟫ⁿ [ ([ TL ] ++ sels) ]≔ⁿ
         (⟪ TL ∷ sels ++ [ HD ] ⟫ⁿ ∷ⁿ ⟪ TL ∷ sels ++ [ TL ] ⟫ⁿ) ⌉⟧
       (v1 ∷ˣ v2) !! [ TL ]
      ≡⟨ refl ⟩
    ⟦⌈ [ [ TL ] ++ sels ]≔∷ⁿ ⌉⟧ (v1 ∷ˣ v2) !! [ TL ]
      ≡⟨ []≔∷ⁿ∘++ (v1 ∷ˣ v2) [ TL ] sels ⟩
    ⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ (v2 !! [])
      ≡⟨ refl ⟩
    ⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ v2
      ≡⟨ ⟦⌈⌉⟧∘≔∷ⁿ sels v2 h ⟩
    v2
    ∎

⟦⌈⌉⟧∘≔∷ⁿ sels ↯ˣ h
  rewrite  ↯ˣ-!! sels
  = ⊥-elim (∷ˣ≢↯ˣ (sym h))

-- condPropagatorsPreserveEval

condPropagatorsPreserveEval :
  (sels : List Selector) (nt1 nt2 : NTrm) (v : Val) →
    ⟦⌈ IfNilⁿ sels (nt1 ○ [ sels ]≔[]ⁿ) (nt2 ○ [ sels ]≔∷ⁿ) ⌉⟧ v
    ≡
    ⟦⌈ IfNilⁿ sels nt1 nt2 ⌉⟧ v

condPropagatorsPreserveEval sels nt1 nt2 v
  rewrite ⟦⟧∘⟪⟫ sels v
  with v !! sels | inspect (_!!_ v) sels 

... | []ˣ | [ ≡[]ˣ ]ⁱ = begin
  ⟦⌈ nt1 ○ [ sels ]≔[]ⁿ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○ nt1 ([ sels ]≔[]ⁿ) v ⟩
  ⟦⌈ nt1 ⌉⟧ (⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ v)
    ≡⟨ cong ⟦⌈ nt1 ⌉⟧ (⟦⌈⌉⟧∘[]≔[]ⁿ sels v ≡[]ˣ) ⟩
  ⟦⌈ nt1 ⌉⟧ v
  ∎

... | _ ∷ˣ _ | [ ≡∷ˣ ]ⁱ = begin
  ⟦⌈ nt2 ○ [ sels ]≔∷ⁿ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘○ nt2 ([ sels ]≔∷ⁿ) v ⟩
  ⟦⌈ nt2 ⌉⟧ (⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ v)
    ≡⟨ cong ⟦⌈ nt2 ⌉⟧ (⟦⌈⌉⟧∘≔∷ⁿ sels v ≡∷ˣ) ⟩
  ⟦⌈ nt2 ⌉⟧ v   
  ∎

... | ↯ˣ | _ = refl

-- propagateIfCond

propagateIfCond : (nt : NTrm) → NTrm

propagateIfCond []ⁿ = []ⁿ
propagateIfCond (nt1 ∷ⁿ nt2) =
  propagateIfCond nt1 ∷ⁿ propagateIfCond nt2
propagateIfCond ⟪ sels ⟫ⁿ = ⟪ sels ⟫ⁿ
propagateIfCond (IfNilⁿ sels nt1 nt2) =
  IfNilⁿ sels
    (propagateIfCond nt1 ○ [ sels ]≔[]ⁿ)
    (propagateIfCond nt2 ○ [ sels ]≔∷ⁿ)
propagateIfCond ↯ⁿ = ↯ⁿ

--
-- ⟦⌈⌉⟧∘propagateIfCond
--

⟦⌈⌉⟧∘propagateIfCond : (nt : NTrm) (v : Val) →
  ⟦⌈ propagateIfCond nt ⌉⟧ v ≡ ⟦⌈ nt ⌉⟧ v

⟦⌈⌉⟧∘propagateIfCond []ⁿ v = refl

⟦⌈⌉⟧∘propagateIfCond (nt1 ∷ⁿ nt2) v
  rewrite ⟦⌈⌉⟧∘propagateIfCond nt1 v
        | ⟦⌈⌉⟧∘propagateIfCond nt2 v
 = refl

⟦⌈⌉⟧∘propagateIfCond ⟪ sels ⟫ⁿ v = refl

⟦⌈⌉⟧∘propagateIfCond (IfNilⁿ sels nt1 nt2) v = begin
  ⟦⌈ propagateIfCond (IfNilⁿ sels nt1 nt2) ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ IfNilⁿ sels (propagateIfCond nt1 ○ [ sels ]≔[]ⁿ)
                 (propagateIfCond nt2 ○ [ sels ]≔∷ⁿ) ⌉⟧ v
    ≡⟨ refl ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ propagateIfCond nt1 ○ [ sels ]≔[]ⁿ ⌉⟧ v)
        (⟦⌈ propagateIfCond nt2 ○ [ sels ]≔∷ⁿ ⌉⟧ v)
    ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
             (⟦⌈⌉⟧∘○ (propagateIfCond nt1) [ sels ]≔[]ⁿ v)
             (⟦⌈⌉⟧∘○ (propagateIfCond nt2) [ sels ]≔∷ⁿ v) ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ propagateIfCond nt1 ⌉⟧ (⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ v))
        (⟦⌈ propagateIfCond nt2 ⌉⟧ (⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ v))
    ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
             (⟦⌈⌉⟧∘propagateIfCond nt1 (⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ v))
             (⟦⌈⌉⟧∘propagateIfCond nt2 (⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ v)) ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ nt1 ⌉⟧ (⟦⌈ [ sels ]≔[]ⁿ ⌉⟧ v))
        (⟦⌈ nt2 ⌉⟧ (⟦⌈ [ sels ]≔∷ⁿ ⌉⟧ v))
    ≡⟨ cong₂ (ifNil (⟦ ⟪ sels ⟫ ⟧ v))
             (sym $ ⟦⌈⌉⟧∘○ nt1 ([ sels ]≔[]ⁿ) v)
             (sym $ ⟦⌈⌉⟧∘○ nt2 ([ sels ]≔∷ⁿ) v) ⟩
  ifNil (⟦ ⟪ sels ⟫ ⟧ v)
        (⟦⌈ nt1 ○ [ sels ]≔[]ⁿ ⌉⟧ v)
        (⟦⌈ nt2 ○ [ sels ]≔∷ⁿ ⌉⟧ v)
    ≡⟨ refl ⟩
  ⟦⌈ IfNilⁿ sels (nt1 ○ [ sels ]≔[]ⁿ)
                 (nt2 ○ [ sels ]≔∷ⁿ) ⌉⟧ v
    ≡⟨ condPropagatorsPreserveEval sels nt1 nt2 v ⟩
  ⟦⌈ IfNilⁿ sels nt1 nt2 ⌉⟧ v
  ∎

⟦⌈⌉⟧∘propagateIfCond ↯ⁿ v = refl


-----------------
-- Normalization
-----------------

-- We can combine the first two stages - normalization and
-- positive information propagation - into a single function,
-- and trivially establish its correctness.

-- norm

norm : (t : Trm) → NTrm
norm t = propagateIfCond ⌋ t ⌊

--
-- `norm` is correct with respect to ⟦⌈_⌉⟧_
--

-- ⟦⌈⌉⟧∘norm

⟦⌈⌉⟧∘norm : ∀ t v → ⟦⌈ norm t ⌉⟧ v ≡ ⟦ t ⟧ v

⟦⌈⌉⟧∘norm t v = begin
  ⟦⌈ norm t ⌉⟧ v
    ≡⟨ refl ⟩
  ⟦⌈ propagateIfCond ⌋ t ⌊ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘propagateIfCond ⌋ t ⌊ v ⟩
  ⟦⌈ ⌋ t ⌊ ⌉⟧ v
    ≡⟨ ⟦⌈⌉⟧∘⌋⌊ t v ⟩
  ⟦ t ⟧ v
  ∎

--
