module Example ( rev ) where

import MAlonzo.Code.Example

rev :: [a] -> [a]
rev = rev' () ()
