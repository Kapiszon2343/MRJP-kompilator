module Common where

import Data.Map

import Latte.Abs
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Bifunctor
import Text.Read (readMaybe)
import Data.Array (Array)

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

showPos :: BNFC'Position -> String
showPos (Just (line, column)) = "(line: " ++ show line ++ ", column: " ++ show column ++ ")"
showPos Nothing = "unknown position"

showIdent :: Ident -> String
showIdent (Ident str) = str

showTypes :: [Type] -> String
showTypes [] = ""
showTypes [tp] = showType tp
showTypes (tp:tail) = showType tp ++ ", " ++ showTypes tail

showType :: Type -> String
showType (Class _ ident) = showIdent ident
showType (Array _ tp) = showType tp ++ "[]"
showType (Int _) = "int"
showType (Str _) = "string"
showType (Bool _) = "bool"
showType (Void _) = "void"
showType (Fun _ retTp argTps) = showType retTp ++ "(" ++ showTypes argTps ++  ")"

showVar :: Var -> String
showVar (IdentVar _ ident) = showIdent ident
showVar (ArrayVar _ var _) = showVar var ++ "[int]"
showVar (AttrVar _ var ident) = showVar var ++ "." ++ showIdent ident

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