module Common where

import Data.Map

import Latte.Abs
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Bifunctor
import Text.Read (readMaybe)
import Data.Array (Array)

type ClassForm = (Data.Map.Map Ident (Type, Int), Int)
type EnvLoc = Data.Map.Map Ident Loc
type EnvClass = Data.Map.Map Ident ClassForm

type Index = Integer
type Loc = Int
type Env = (EnvLoc, EnvClass)

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

builtInFunctions :: [BuiltInFunction]
builtInFunctions = [
    (Ident "printInt", Fun Nothing (Void Nothing) [Int Nothing], BStr ""),
    (Ident "printString", Fun Nothing (Void Nothing) [Str Nothing], BStr ""),
    (Ident "error", Fun Nothing (Void Nothing) [], BStr ""),
    (Ident "readInt", Fun Nothing (Int Nothing) [], BStr ""),
    (Ident "readString", Fun Nothing (Str Nothing) [], BStr "")
    ]

data Val = ValBool Bool
    | ValInt Integer
    | ValStr String
    | ValUndef

instance Eq Val where
    ValBool b0 == ValBool b1 = b0 == b1
    ValInt n0 == ValInt n1 = n1 == n0
    ValStr str0 == ValStr str1 = str0 == str1
    _ == _ = False

defaultVal :: Type -> Val
defaultVal (Class _ _) = ValUndef
defaultVal (Array _ _) = ValUndef
defaultVal (Int _) = ValInt 0
defaultVal (Bool _) = ValBool False
defaultVal (Str _) = ValStr ""
defaultVal (Void _) = ValUndef
defaultVal (Fun {}) = ValUndef

preEval :: Expr -> Val
preEval (ENew _pos new) = ValUndef
preEval (EVar _pos var) = ValUndef
preEval (ELitInt _pos n) = ValInt n 
preEval (ELitTrue _pos) = ValBool True
preEval (ELitFalse _pos) = ValBool False
preEval (ELitArr _pos expr) = ValUndef
preEval (EApp _pos var expr) = ValUndef
preEval (EString _pos str) = ValStr str
preEval (Neg _pos expr) =  case preEval expr of
    ValInt n -> ValInt $ -n
    _ -> ValUndef
preEval (Not _pos expr) =  case preEval expr of
    ValBool bol -> ValBool $ not bol
    _ -> ValUndef
preEval (EMul _pos expr0 op expr1) = case preEval expr0 of
    ValInt n0 -> case preEval expr1 of
        ValInt n1 -> case op of
            Times _ -> ValInt $ n0 * n1
            Div _ -> ValInt $ div n0 n1
            Mod _ -> ValInt $ mod n0 n1
        _ -> ValUndef
    _ -> ValUndef
preEval (EAdd _pos expr0 op expr1) = case preEval expr0 of
    ValInt n0 -> case preEval expr1 of
        ValInt n1 -> case op of
            Plus _ -> ValInt $ n0 + n1
            Minus _ -> ValInt $ n0 - n1
        _ -> ValUndef
    ValStr str0 -> case preEval expr1 of
        ValStr str1 -> case op of
            Plus _ -> ValStr $ str0 ++ str1
            _ -> ValUndef
        _ -> ValUndef 
    _ -> ValUndef
preEval (ERel _pos expr0 op expr1) = case op of
    EQU _ -> ValBool $ preEval expr0 == preEval expr1
    NE _ -> ValBool $ preEval expr0 /= preEval expr1
    _ -> case preEval expr0 of
        ValInt n0 -> case preEval expr1 of
            ValInt n1 -> case op of
                LTH _ -> ValBool $ n0 < n1
                LE _ -> ValBool $ n0 <= n1
                GTH _ -> ValBool $ n0 > n1
                GE _ -> ValBool $ n0 >= n1
            _ -> ValUndef
        _ -> ValUndef
preEval (EAnd _pos expr0 expr1) = case preEval expr0 of
    ValBool b0 -> case preEval expr1 of
        ValBool b1 -> ValBool $ b0 && b1
        _ -> ValUndef
    _ -> ValUndef
preEval (EOr _pos expr0 expr1) = case preEval expr0 of
    ValBool b0 -> case preEval expr1 of
        ValBool b1 -> ValBool $ b0 || b1
        _ -> ValUndef
    _ -> ValUndef

data StringBuilder 
    = BStr String
    | BLst [StringBuilder]

addString :: String -> StringBuilder -> String
addString baseStr (BStr str) = str ++ baseStr
addString baseStr (BLst []) = baseStr
addString baseStr (BLst (builder:lst)) = addString (addString baseStr (BLst lst)) builder

buildString :: StringBuilder -> String
buildString = addString ""