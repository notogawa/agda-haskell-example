-- agda -c -isrc -i/usr/share/agda-stdlib/ src/Main.agda
module Main where

open import IO
open import Function
open import Coinduction
open import Data.String using (String; toList; fromList)
open import Example

-- main = interact $ unline . reverse . lines
main = run (♯ getContents >>= ♯_ ∘ eachline ( fromList ∘ rev ∘ toList) ) where

  open import Data.Maybe
  open import Data.Product
  open import Data.List using ([]; _∷_; [_])
  open import Data.Colist using (Colist; []; _∷_)
  open import Data.String using (Costring; _++_)
  open import Data.Unit using (⊤; tt)
  open import Category.Monad.Partiality

  takeLine : Costring → Maybe (String × ∞ Costring) ⊥
  takeLine [] = now nothing -- EOF
  takeLine xs = go "" xs where
    go : String → Costring → Maybe (String × ∞ Costring) ⊥
    go acc [] = now (just (acc , ♯ []))
    go acc (x ∷ xs) with fromList [ x ]
    go acc (_ ∷ xs) | "\n" = now (just (acc , xs))
    go acc (_ ∷ xs) | last = later (♯ go (acc ++ last) (♭ xs))

  takeLine' : Costring → (String × Costring) ⊥
  takeLine' xs = go "" xs where
    go : String → Costring → (String × Costring) ⊥
    go acc [] = now (acc , [])
    go acc (x ∷ xs) with fromList [ x ]
    go acc (x ∷ xs) | "\n" = now (acc , (♭ xs))
    go acc (x ∷ xs) | last = later (♯ go (acc ++ last) (♭ xs))

  eachline : (String → String) → Costring → IO ⊤
  eachline f = go ∘ takeLine where
    go : Maybe (String × ∞ Costring) ⊥ → IO ⊤
    go (now nothing) = return tt
    go (now (just (line , xs))) = ♯ putStrLn (f line) >> ♯ go (takeLine (♭ xs))
    go (later x) = ♯ return tt >> ♯ go (♭ x)

  eachline' : (String → String) → Costring → IO ⊤
  eachline' f = go ∘ takeLine' where
    go : (String × Costring) ⊥ → IO ⊤
    go (now (line , xs)) = ♯ putStrLn (f line) >> ♯ go (takeLine' xs)
    go (later x) = ♯ return tt >> ♯ go (♭ x)
