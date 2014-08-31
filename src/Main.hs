module Main where

import Example

main :: IO ()
main = interact $ unlines . map reverse . lines
