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
import Distribution.System (OS(Windows, Linux), buildOS)
import qualified Data.Set
import Data.Bifunctor (first, Bifunctor (second, bimap))

type StructDepth = Int
type MethodDepth = Int
data AttrLoc = Inline
    | AttrLocVar StructDepth
    | AttrLocMet MethodDepth
type ClassSize = (StructDepth, MethodDepth)
type ClassAttrs = Data.Map.Map Ident (Type, AttrLoc)
type ClassForm = (ClassAttrs, Data.Map.Map MethodDepth (Ident, Ident), ClassSize)
type EnvLoc = Data.Map.Map Ident Loc
type EnvClass = Data.Map.Map Ident (ClassForm, Ident)

type Index = Integer
type Loc = Int
type Env = (EnvLoc, EnvClass)

type BuiltInFunction = (Ident, Type, StringBuilder, StringBuilder)

type Reg = Int
data RegLoc = Reg Reg
    | RBP Int
    | Lit Int
    | Mem Int RegLoc RegLoc Int
    deriving (Show, Eq)

triMap fa fb fc (a,b,c) = (fa a, fb b, fc c)

showRegLoc (Reg r) = showReg r
showRegLoc (RBP n) = show (-n) ++ "(%rbp)"
showRegLoc (Lit n) = "$" ++ show n
showRegLoc (Mem a ref (Lit b) c) = do
    let x = a + b*c
    if x == 0
        then "(" ++ showRegLoc ref ++ ")"
        else show x ++ "(" ++ showRegLoc ref ++ ")"
showRegLoc (Mem 0 ref counter m) = "(" ++ showRegLoc ref ++ ", " ++ showRegLoc counter ++ ", " ++ show m ++ ")"
showRegLoc (Mem n ref counter m) = show n ++ "(" ++ showRegLoc ref ++ ", " ++ showRegLoc counter ++ ", " ++ show m ++ ")"

isRegLocLocal (Reg _) = True
isRegLocLocal (Lit _) = True
isRegLocLocal _ = False

isRegLocReg (Reg _) = True
isRegLocReg _ = False

rsp :: Reg
rsp = 0
rbp :: Reg
rbp = 1
rbx :: Reg
rbx = 2
rax :: Reg
rax = 3
rdx :: Reg
rdx = 4
rsi :: Reg
rsi = 5
rdi :: Reg
rdi = 6
rcx :: Reg
rcx = 7
r8 :: Reg
r8 = 8
r9 :: Reg
r9 = 9
r10 :: Reg
r10 = 10
r11 :: Reg
r11 = 11

showReg :: Reg -> String
showReg 0 = "%rsp"
showReg 1 = "%rbp"
showReg 2 = "%rbx"
showReg 3 = "%rax"
showReg 4 = "%rdx"
showReg 5 = "%rsi"
showReg 6 = "%rdi"
showReg 7 = "%rcx"
showReg r = "%r" ++ show r

globalSelfRegLoc :: RegLoc
globalSelfRegLoc = Reg $ head stableRegs
globalIdentSelf = Ident "self"
stableRegs :: [Reg]
stableRegs = [12..15]
tmpRegs :: [Reg]
tmpRegs = [rdi, rsi, rdx, rcx, r8, r9, r10, r11]
argRegs :: [Reg]
argRegs = case buildOS of
    Windows -> [rcx, rdx, r8, r9]
    Linux -> [rdi, rsi, rdx, rcx, r8, r9]
argRegCount = length argRegs
argRegLoc0 = Reg $ head argRegs
argRegLoc1 = Reg $ argRegs!!1
argRegLoc2 = Reg $ argRegs!!2
argRegLoc3 = Reg $ argRegs!!3

moveRegsLocs :: RegLoc -> RegLoc -> StringBuilder
moveRegsLocs (Lit 0) (Reg r) = BStr $ "\txorq " ++ showReg r ++ ", " ++ showReg r ++ "\n"
moveRegsLocs (Lit n) regLoc = BStr $ "\tmovq " ++ showRegLoc (Lit n) ++ ", " ++ showRegLoc regLoc ++ "\n"
moveRegsLocs (Reg r) regLoc = if Reg r /= regLoc
                                then BStr $ "\tmovq " ++ showReg r ++ ", " ++ showRegLoc regLoc ++ "\n"
                                else BLst []
moveRegsLocs regLoc (Reg r) = if regLoc /= Reg r 
                                then BStr $ "\tmovq " ++ showRegLoc regLoc ++ ", " ++ showReg r ++ "\n"
                                else BLst []
moveRegsLocs regLoc1 regLoc2 = if regLoc1 /= regLoc2
                                then BStr $ "\tmovq " ++ showRegLoc regLoc1 ++ ", " ++ showReg rax ++ "\n"
                                    ++ "\tmovq " ++ showReg rax ++ ", " ++ showRegLoc regLoc2 ++ "\n"
                                else BLst []

extractMemIt :: RegLoc -> RegLoc -> RegLoc
extractMemIt (Mem dipl regLocPointer regLocIt step) _ = regLocIt
extractMemIt _ def = def

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

classLabel :: Ident -> String
classLabel classIdent = "class_" ++ showIdent classIdent

destructorLabel :: Ident -> String
destructorLabel classIdent = "classDestructor_" ++ showIdent classIdent

labelLine :: String -> StringBuilder
labelLine label = BStr $ label ++ ":\n"

builtInFunctions :: [BuiltInFunction]
builtInFunctions = [
    (Ident "printInt", Fun Nothing (Void Nothing) [Int Nothing], BStr 
        $ "fun_printInt:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tmov " ++ showRegLoc argRegLoc0 ++ ", " ++ showRegLoc argRegLoc1 ++ "\n"
        ++ "\tleaq .printInt(%rip), " ++ showRegLoc argRegLoc0 ++ "\n"
        ++ "\tcall printf\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n",
        BStr ".printInt: .ascii \"%d\\n\\0\"\n"),
    (Ident "printString", Fun Nothing (Void Nothing) [Str Nothing], BStr
        $ "fun_printString:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tmov " ++ showRegLoc argRegLoc0 ++ ", " ++ showRegLoc argRegLoc1 ++ "\n"
        ++ "\tadd $8, " ++ showRegLoc argRegLoc1 ++ "\n"
        ++ "\tleaq .printString(%rip), " ++ showRegLoc argRegLoc0 ++ "\n"
        ++ "\tcall printf\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n",
        BStr ".printString: .ascii \"%s\\n\\0\"\n"),
    (Ident "error", Fun Nothing (Void Nothing) [], BStr
        $ "fun_error:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tleaq .error(%rip), " ++ showRegLoc argRegLoc0 ++ "\n"
        ++ "\tcall printf\n"
        ++ "\tmov $60, %rax\n"
        ++ "\tmov $0, " ++ showRegLoc argRegLoc0  ++ "\n"
        ++ "\tsyscall\n",
        BStr ".error: .ascii \"runtime error\\n\\0\"\n"),
    (Ident "readInt", Fun Nothing (Int Nothing) [], BStr 
        $ "fun_readInt:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tleaq .readInt(%rip), " ++ showRegLoc argRegLoc0 ++ "\n"
        ++ "\tmov %rsp, " ++ showRegLoc argRegLoc1 ++ "\n"
        ++ "\tcall scanf\n"
        ++ "\tmov 0(%rsp), %rax\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n", 
        BStr ".readInt: .ascii \"%d\\0\"\n"),
    (Ident "readString", Fun Nothing (Str Nothing) [], BStr 
        $ "fun_readString:\n"
        ++ "\tpush %rbp\n"
        ++ "\tmov %rsp, %rbp\n"
        ++ "\tsub $32, %rsp\n"
        ++ "\tmov $64, " ++ showRegLoc argRegLoc0 ++ "\n"
        ++ "\tcall malloc\n"
        ++ "\tmov %rax, 8(%rsp)\n"
        ++ "\tmov %rax, " ++ showRegLoc argRegLoc1 ++ "\n"
        ++ "\tadd $8, " ++ showRegLoc argRegLoc1 ++ "\n"
        ++ "\tleaq .readString(%rip), " ++ showRegLoc argRegLoc0 ++ "\n"
        ++ "\tcall scanf\n"
        ++ "\tmov 8(%rsp), %rax\n"
        ++ "\tmovq $0, (%rax)\n"
        ++ "\tadd $32, %rsp\n"
        ++ "\tmov %rbp, %rsp\n"
        ++ "\tpop %rbp\n"
        ++ "\tret\n", 
        BStr ".readString: .ascii \"%s\\0\"\n")
    ]

perfectMatchType :: Type' a -> Type' a -> Bool
perfectMatchType (Int _) (Int _) = True
perfectMatchType (Str _) (Str _) = True
perfectMatchType (Bool _) (Bool _) = True
perfectMatchType (Void _) (Void _) = True
perfectMatchType (Fun _ ret1 []) (Fun _ ret2 []) = perfectMatchType ret1 ret2
perfectMatchType (Fun pos1 ret1 (arg1:args1)) (Fun pos2 ret2 (arg2:args2)) =
    perfectMatchType arg1 arg2 && perfectMatchType (Fun pos1 ret1 args1) (Fun pos2 ret2 args2)
perfectMatchType (Array _ tp1) (Array _ tp2) = perfectMatchType tp1 tp2
perfectMatchType (Class pos1 (Ident str1)) (Class pos2 (Ident str2)) = str1 == str2
perfectMatchType _ _ = False

jmpSize = 5
labelSize = 8
methodDepthStep = labelSize

formClass'' :: Ident -> ClassForm -> [ClassElem] -> Except String ClassForm
formClass'' classIdent form [] = return form
formClass'' classIdent form (elem:elems) = do
    let (attrMap, methodDepthMap, (structSize, methodSize)) = form
    case elem of
        Attribute pos tp ident -> case Data.Map.lookup ident attrMap of
            Just _ -> formClass'' classIdent (triMap (Data.Map.insert ident (tp, AttrLocVar structSize)) id (first (+8)) form) elems
            Nothing -> formClass'' classIdent (triMap (Data.Map.insert ident (tp, AttrLocVar structSize)) id (first (+8)) form) elems
        Method pos retTp ident args block -> case Data.Map.lookup ident attrMap of
            Just (tp, attrLoc) -> case attrLoc of
                AttrLocMet depth -> do
                    let newTp = Fun pos retTp $ Prelude.foldl (\tps arg -> argToType arg:tps) [] args
                    if perfectMatchType tp newTp
                        then formClass'' classIdent (triMap
                            (Data.Map.insert ident (tp, AttrLocMet depth))
                            (Data.Map.insert depth (ident, classIdent))
                            id
                            form) elems
                        else throwError $ "Function type mismatch at function overwrite: " ++ showIdent ident ++ "\n"
                            ++ "old type: " ++ showType tp ++ "\n"
                            ++ "new type: " ++ showType newTp ++ "\n"
                            ++ " at: " ++ showPos pos
                _ -> throwError $ "Overwriting function with non function: " ++ showIdent ident ++ " at: " ++ showPos pos
            Nothing -> formClass'' classIdent (triMap
                (Data.Map.insert ident (Fun pos retTp $ Prelude.foldl (\tps arg -> argToType arg:tps) [] args, AttrLocMet methodSize))
                (Data.Map.insert methodSize (ident, classIdent))
                (second (+methodDepthStep))
                form) elems

checkClassElems' :: Data.Set.Set Ident -> [ClassElem] -> Except String ()
checkClassElems' elemSet [] = return ()
checkClassElems' elemSet (elem:elems) = do
    let (pos, ident) = case elem of 
            Attribute pos tp ident -> (pos, ident)
            Method pos retTp ident args block -> (pos, ident)
    if Data.Set.member ident elemSet
        then throwError $ "Multiple definitions of: " ++ showIdent ident ++ "  at: " ++ showPos pos
        else checkClassElems' (Data.Set.insert ident elemSet) elems

checkClassElems = checkClassElems' Data.Set.empty

formClass' :: Ident -> ClassForm -> [ClassElem] -> Except String ClassForm
formClass' classIdent form elems = do
    checkClassElems elems
    formClass'' classIdent form elems

formClass :: Ident -> [ClassElem] -> Except String ClassForm
formClass classIdent = formClass' classIdent (Data.Map.empty, Data.Map.empty, (16, methodDepthStep))

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