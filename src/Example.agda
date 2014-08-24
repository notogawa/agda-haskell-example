module Example where

open import Data.List

-- reverse
rev : ∀ {a} {A : Set a} → List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ [ x ]

-- https://code.google.com/p/agda/issues/detail?id=1252 暫定対策
rev' = rev

{-# COMPILED_EXPORT rev' rev' #-}

private
  -- reverse2回で元に戻る証明
  open import Relation.Binary.PropositionalEquality

  lemma : ∀ {a} {A : Set a} (x : A) (xs : List A) → rev (xs ∷ʳ x) ≡ x ∷ rev xs
  lemma x [] = refl
  lemma x (_ ∷ xs)
    rewrite lemma x xs
          = refl

  revrev-is-id : ∀ {a} {A : Set a} (xs : List A) → rev (rev xs) ≡ xs
  revrev-is-id [] = refl
  revrev-is-id (x ∷ xs)
    rewrite lemma x (rev xs)
          | revrev-is-id xs
          = refl
