module Common where

import Data.Map

import Latte.Abs
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
    = BStr String
    | BLst [StringBuilder]

addString :: String -> StringBuilder -> String
addString baseStr (BStr str) = str ++ baseStr
addString baseStr (BLst []) = baseStr
addString baseStr (BLst (builder:lst)) = addString (addString baseStr (BLst lst)) builder

buildString :: StringBuilder -> String
buildString = addString ""