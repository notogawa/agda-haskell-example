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
  open import Relation.Binary.PropositionalEquality

  -- reverse2回で元に戻る証明
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

open import Data.Empty

head : ∀ {a} {A : Set a} (xs : List A) → {xs≢[] : xs ≢ []} → A
head [] {xs≠[]} = ⊥-elim (xs≠[] refl)
head (x ∷ xs) = x
{-
{-# COMPILED_EXPORT head safeHead' #-}
-- エラーになる
-- The type _≡_ cannot be translated to a Haskell type.
-- when checking the pragma COMPILED_EXPORT head' safeHead
--
-- つまり，証明オブジェクトを取るような関数は，
-- そのままではCOMPILED_EXPORTできないことが多い
-}

open import Data.Maybe

head' : ∀ {a} {A : Set a} (xs : List A) → Maybe A
head' = go where
  go : ∀ {a} {A : Set a} (xs : List A) → Maybe A
  go [] = nothing
  go (x ∷ xs) = just (head (x ∷ xs) {λ ()})
{-# COMPILED_EXPORT head' safeHead' #-}
-- つまり，安全なheadを使うには，
-- 安全なものだけ渡せるようにしてjustで結果が得られ，
-- それ以外についてはnothingになるように，
-- 適切にラップしないとCOMPILED_EXPORTできない．
