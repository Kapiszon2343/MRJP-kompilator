module Common where

import Data.Map

import Instant.Abs
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Bifunctor
import Text.Read (readMaybe)

type Index = Integer
type Loc = Int
type Env = Data.Map.Map Ident Loc

identStr :: Ident -> String
identStr (Ident str) = str

data StringBuilder 
    = Str String
    | Lst [StringBuilder]

addString :: String -> StringBuilder -> String
addString baseStr (Str str) = str ++ baseStr
addString baseStr (Lst []) = baseStr
addString baseStr (Lst (builder:lst)) = addString (addString baseStr (Lst lst)) builder

buildString :: StringBuilder -> String
buildString = addString ""