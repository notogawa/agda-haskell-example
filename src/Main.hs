module Main where

import Example

main :: IO ()
main = do
  print $ rev [1..5]
  print $ safeHead [1..5]
