module Compiler where

import Data.Map
import Data.Maybe (fromMaybe)
import Data.Bifunctor ( first )
import Control.Monad.State
import Control.Monad.Reader ( ReaderT (runReaderT), MonadReader(local, ask), asks )
import Control.Monad.Except

import Latte.Abs
import Common
import qualified Text.ParserCombinators.ReadP as Data.Map
import GHC.IO.Handle.Internals (readTextDevice)

type Reg = Int

data RegLoc = Reg Reg
    | RSP Int
instance Eq RegLoc where
    Reg regNr0 == Reg regNr1 = regNr0 == regNr1
    RSP offset0 == RSP offset1 = offset0 == offset1
    _ == _ = False
instance Ord RegLoc where
    compare (Reg r0) (Reg r1) = compare r0 r1
    compare (RSP r0) (RSP r1) = compare r1 r0
    compare (Reg _) (RSP _) = LT
    compare (RSP _) (Reg _) = GT
type VariableRegisterLoc = Data.Map.Map Loc RegLoc 
type RegisterLocUse = Data.Map.Map RegLoc Int
type CompilerStore = (VariableRegisterLoc, RegisterLocUse, Loc, Int)

type VarVal = Integer

type CompilerMonad = ExceptT String (ReaderT Env (StateT CompilerStore IO))

type Ret = (Env -> Env, VarVal)

rax :: Reg
rax = 3
rcx = 7
rdx = 4

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

showRegLoc (Reg r) = showReg r
showRegLoc (RSP n) = "[%rsp-" ++ show n ++ "]"

argRegLoc :: Int -> RegLoc
argRegLoc n = case n of
    0 -> Reg rax
    1 -> Reg rcx
    2 -> Reg rdx
    3 -> Reg 8
    4 -> Reg 9
    _ -> RSP ((n - 5) * 8)

argReg = [rcx, rdx, 8, 9]
stableReg = [10..15]
allUsableRegLocs = [rax..15] -- TODO all registers
argRegLocs = argRegLocs' argReg

argRegLocs' = Prelude.foldr ((:) . Reg) (argRegLocs'' 0)

argRegLocs'' :: Int -> [RegLoc]
argRegLocs'' n = RSP n:argRegLocs'' (n+8)

lookupInt :: Ord k => k -> Data.Map.Map k Int -> Int
lookupInt k mp = fromMaybe 0 $ Data.Map.lookup k mp

newloc :: CompilerMonad Loc
newloc = do
    (vrc, rlu, nextLoc, rspSize) <- get
    put (vrc, rlu, nextLoc+1, rspSize)
    return nextLoc
{-
freeRegLocs':: [RegLoc] -> [RegLoc] -> [RegLoc]
freeRegLocs' [] uncheckedRegLocs = uncheckedRegLocs
freeRegLocs' (takenRegLoc:takenRegLocs) (uncheckedRegLoc:uncheckedRegLocs) = if takenRegLoc == uncheckedRegLoc
    then freeRegLocs' takenRegLocs uncheckedRegLocs
    else uncheckedRegLoc:freeRegLocs' takenRegLocs uncheckedRegLocs

freeRegLocs :: CompilerMonad [RegLoc]
freeRegLocs = do 
    (mem, l, m) <- get
    return $ freeRegLocs' (Data.Map.elems mem) allRegLocs
-}
getFreeReg' :: Reg -> CompilerMonad Reg
getFreeReg' r = do
    if r > 9
        then throwError "unimplemented"
        else do
            (vrc, rlu, nextLoc, rspSize) <- get
            case lookupInt (Reg r) rlu of
                0 -> return r
                _ -> getFreeReg' (r+1)

getFreeReg :: CompilerMonad Reg
getFreeReg = getFreeReg' rax

freeReg :: Reg -> CompilerMonad StringBuilder
freeReg r = do
    -- TODO actually free register
    return $ BStr ""
    

getLoc :: BNFC'Position -> Ident -> CompilerMonad Loc 
getLoc pos ident = do
    (envLoc, envClass) <- ask
    case Data.Map.lookup ident envLoc of
        Just loc -> return loc
        Nothing -> throwError ("undefined variable " ++ show ident ++ " at " ++ show pos)

getIdentLoc :: BNFC'Position -> Ident -> CompilerMonad Loc
getIdentLoc pos ident = do
    getLoc pos ident

compileExpr' :: Expr -> Reg -> CompilerMonad StringBuilder
compileExpr' (ELitInt pos n) r = do
    return $ BStr $ "\tmov $" ++ show n ++ ", " ++ showReg r ++ "\n"
compileExpr' (ELitTrue pos) r = compileExpr' (ELitInt pos 1) r
compileExpr' (ELitFalse pos) r = compileExpr' (ELitInt pos 0) r
compileExpr' expr r = do
    (code, rr) <- compileExpr expr
    return $ BLst [
            code,
            BStr $ "\tmov " ++ showReg rr ++ ", " ++ showReg r ++ "\n"
        ]

fillArgs :: [RegLoc] -> [Expr] -> CompilerMonad StringBuilder
fillArgs ((Reg reg):regLocs) (expr:exprs) = do
    freeReg reg
    exprCode <- compileExpr' expr reg
    tailCode <- fillArgs regLocs exprs
    return $ BLst [
            exprCode,
            tailCode
        ]
fillArgs ((RSP rsp):regLocs) (expr:exprs) = do
    freeReg rax
    exprCode <- compileExpr' expr rax
    tailCode <- fillArgs regLocs exprs
    return $ BLst [
            exprCode,
            BStr $ "\tmov %rax, " ++ showRegLoc (RSP rsp) ++ "\n",
            tailCode
        ]
fillArgs regLocs [] = return $ BLst []

compileExpr :: Expr -> CompilerMonad (StringBuilder, Reg)
compileExpr (ENew pos newVar) = throwError "unimplemented"
compileExpr (EVar pos var) = throwError "unimplemented"
-- compileExpr (ELitInt pos n) = throwError "unimplemented" -- TODO opt
compileExpr (ELitTrue pos) = compileExpr (ELitInt pos 1)
compileExpr (ELitFalse pos) = compileExpr (ELitInt pos 0)
compileExpr (ELitArr pos elems) = throwError "unimplemented"
compileExpr (ELitNull pos classIdent) = throwError "unimplemented"
compileExpr (EApp pos var exprs) = do
    freeCode <- freeReg rax
    fillCode <- fillArgs argRegLocs exprs
    return (
            BLst [
                freeCode,
                fillCode,
                BStr $ "\tcall " ++ showVar var ++ "\n" -- TODO Maybe check for arrays
            ],
            rax
        )
compileExpr (EString pos str) = throwError "unimplemented"
compileExpr (Neg pos expr) = throwError "unimplemented"
compileExpr (Not pos expr) = throwError "unimplemented"
compileExpr (EMul pos expr0 op expr1) = throwError "unimplemented"
compileExpr (EAdd pos expr0 op expr1) = throwError "unimplemented"
compileExpr (ERel pos expr0 op expr1) = throwError "unimplemented"
compileExpr (EAnd pos expr0 expr1) = throwError "unimplemented"
compileExpr (EOr pos expr0 expr1) = throwError "unimplemented"
compileExpr expr = do
    r <- getFreeReg
    code <- compileExpr' expr r
    return (code, r)

compileStmt :: Stmt -> CompilerMonad StringBuilder
compileStmt (Empty pos) = return $ BLst []
compileStmt (BStmt pos (Block _bPos [])) = do
    return $ BStr ""
compileStmt (BStmt pos (Block _bPos (stmt:stmts))) = do
    code1 <- compileStmt stmt
    code2 <- compileStmt (BStmt pos (Block _bPos stmts))
    return $ BLst [
            code1,
            code2
        ]
compileStmt (Decl pos tp decls) = throwError "unimplemented"
compileStmt (Ass pos ident expr) = throwError "unimplemented"
compileStmt (Incr pos ident) = throwError "unimplemented"
compileStmt (Decr pos ident) = throwError "unimplemented"
compileStmt (Ret pos expr) = do
    code <- compileExpr' expr rax
    return $ BLst [
            code,
            BFil filRetN
        ]
compileStmt (VRet pos) = return $ BFil filRetN
compileStmt (Cond pos expr stmt) = throwError "unimplemented"
compileStmt (CondElse pos expr stmtTrue stmtFalse) = throwError "unimplemented"
compileStmt (While pos expr stmt) = throwError "unimplemented"
compileStmt (For pos incrTp incrIdent incrSet cond incrStmt blockStmt) = throwError "unimplemented"
compileStmt (ForEach pos elemTp elemIdent arrExpr blockStmt) = throwError "unimplemented"
compileStmt (SExp pos expr) = do
    (code, _r) <- compileExpr expr
    return code


compileTopDefs :: StringBuilder -> [TopDef] -> CompilerMonad StringBuilder
compileTopDefs code ((FnDef pos tp ident args block):lst) = do
    currCode <- compileStmt (BStmt pos block) -- TODO add args, fill filRetN
    (vrc, rlu, nextLoc, rspSizeOld) <- get
    let rspSize = 32 * div (rspSizeOld + 31) 32
    compileTopDefs (BLst [
            code,
            BStr $ showIdent ident ++ ":\n"
                ++ "\tpush %rbp\n"
                ++ "\tmov %rsp, %rbp\n"
                ++ "\tsub $" ++ show rspSize ++ ", %rsp\n",
            fillStringBuilder (Data.Map.singleton filRetN (
                   "\tadd $" ++ show rspSize ++ ", %rsp\n"
                ++ "\tmov %rbp, %rsp\n"
                ++ "\tpop %rbp\n"
                ++ "\tret\n")) currCode
        ]) lst
compileTopDefs code ((ClassDef pos ident elems):lst) = throwError "unimplemented"
compileTopDefs code ((ClassExt pos classIdent parentIdent elems):lst) = throwError "unimplemented"
compileTopDefs code [] = do return code

compileBuiltInFunctions :: [BuiltInFunction] -> CompilerMonad StringBuilder
compileBuiltInFunctions [] = return $ BLst []
compileBuiltInFunctions ((_,_,codeF):tail) = do
    code <- compileBuiltInFunctions tail
    return $ BLst [
            codeF,
            code
        ]

filRetN = 1

compileProgram :: Program -> CompilerMonad String
compileProgram (Program pos topDefs) = do
    buildInCode <- compileBuiltInFunctions builtInFunctions
    code <- compileTopDefs (BLst []) topDefs
    return $ buildString (BLst [
        BStr $ ".data\n"
            ++ ".printInt: .ascii \"%d\\n\\0\"\n", -- TODO make it auto for all string 
        BStr $ ".text\n"
            ++ ".globl main\n",
        buildInCode,
        code
        ])