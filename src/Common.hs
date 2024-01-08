module Common where

import Data.Map

import Latte.Abs
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Bifunctor
import Text.Read (readMaybe)
import Data.Array (Array)
import Data.Maybe

type ClassForm = (Data.Map.Map Ident (Type, Int), Int)
type EnvLoc = Data.Map.Map Ident Loc
type EnvClass = Data.Map.Map Ident (ClassForm, Ident)

type Index = Integer
type Loc = Int
type Env = (EnvLoc, EnvClass)

type BuiltInFunction = (Ident, Type, StringBuilder, StringBuilder)

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
    (Ident "printInt", Fun Nothing (Void Nothing) [Int Nothing], BStr 
        $ "printInt:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tmov %rcx, %rdx\n"
        ++ "\tleaq .printInt(%rip), %rcx\n"
        ++ "\tcall printf\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n",
        BStr ".printInt: .ascii \"%d\\n\\0\"\n"),
    (Ident "printString", Fun Nothing (Void Nothing) [Str Nothing], BStr
        $ "printString:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tcall printf\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n",
        BStr ""),
    (Ident "error", Fun Nothing (Void Nothing) [], BStr
        $ "error:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tleaq .error(%rip), %rcx\n"
        ++ "\tcall printf\n"
        ++ "\tmov $60, %eax\n"
        ++ "\tmov $0, %ebx\n"
        ++ "\tint $0x80\n",
        BStr ".error: .ascii \"runtime error\\n\\0\"\n"),
    (Ident "readInt", Fun Nothing (Int Nothing) [], BStr 
        $ "readInt:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tleaq .readInt(%rip), %rcx\n"
        ++ "\tmov %rsp, %rdx\n"
        ++ "\tcall scanf\n"
        ++ "\tmov 0(%rsp), %rax\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n", 
        BStr ".readInt: .ascii \"%d\\0\"\n"),
    (Ident "readString", Fun Nothing (Str Nothing) [], BStr 
        $ "readString:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tmov $128, %rcx\n"
        ++ "\tcall malloc\n"
        ++ "\tleaq .readString(%rip), %rcx\n"
        ++ "\tmov %rax, %rdx\n"
        ++ "\tcall scanf\n"
        ++ "\tmov %rdx, %rax\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n", 
        BStr ".readString: .ascii \"%s\\0\"\n")
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
preEval (ENeg _pos expr) =  case preEval expr of
    ValInt n -> ValInt $ -n
    _ -> ValUndef
preEval (ENot _pos expr) =  case preEval expr of
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
    | BFil Int

addString :: String -> Data.Map.Map Int String -> StringBuilder -> String
addString baseStr mp (BStr str) = str ++ baseStr
addString baseStr mp (BLst []) = baseStr
addString baseStr mp (BLst (builder:lst)) = addString (addString baseStr mp (BLst lst)) mp builder
addString baseStr mp (BFil n) = addString baseStr mp (BStr $ fromMaybe "" $ Data.Map.lookup n mp)

buildString :: StringBuilder -> String
buildString = addString "" Data.Map.empty

fillStringBuilder :: Data.Map.Map Int String -> StringBuilder -> StringBuilder
fillStringBuilder mp (BStr str) = BStr str
fillStringBuilder mp (BLst []) = BLst []
fillStringBuilder mp (BLst [builder]) = BLst [fillStringBuilder mp builder]
fillStringBuilder mp (BLst (builder:lst)) = do
    let (BLst tail) = fillStringBuilder mp (BLst lst)
    BLst (fillStringBuilder mp builder:tail)
fillStringBuilder mp (BFil n) = BStr $ fromMaybe "" $ Data.Map.lookup n mp

fillString :: Data.Map.Map Int String -> StringBuilder -> String
fillString = addString ""