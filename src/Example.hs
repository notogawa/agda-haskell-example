module Example where

import MAlonzo.Code.Example

rev :: [a] -> [a]
rev = rev' () ()

safeHead :: [a] -> Maybe a
safeHead = safeHead' () ()
