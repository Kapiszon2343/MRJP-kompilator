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

type BuiltInFunction = (Ident, Type, StringBuilder)

argToType :: Arg -> Type
argToType (Arg _pos tp _ident) = tp

argToIdent :: Arg -> Ident
argToIdent (Arg _pos _tp ident) = ident

identStr :: Ident -> String
identStr (Ident str) = str

typePos :: Type -> BNFC'Position
typePos (Class pos _ident) = pos
typePos (Array pos _tp) = pos
typePos (Int pos) = pos
typePos (Str pos) = pos
typePos (Bool pos) = pos
typePos (Void pos) = pos
typePos (Fun pos _tp _tps) = pos

posToStr :: BNFC'Position -> String
posToStr (Just (line, column)) = "(line: " ++ show line ++ ", column: " ++ show column ++ ")"
posToStr Nothing = "unknown position"

builtInFunctions = []

data StringBuilder 
    = BStr String
    | BLst [StringBuilder]

addString :: String -> StringBuilder -> String
addString baseStr (BStr str) = str ++ baseStr
addString baseStr (BLst []) = baseStr
addString baseStr (BLst (builder:lst)) = addString (addString baseStr (BLst lst)) builder

buildString :: StringBuilder -> String
buildString = addString ""