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
type VariableRegisterLoc = Data.Map.Map Ident RegLoc 
type RegisterLocUse = Data.Map.Map RegLoc [Ident]
type StringCodes = (StringBuilder, Int)
type CompilerStore = (VariableRegisterLoc, RegisterLocUse, Loc, Int, StringCodes)

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

lookupArr k mp = fromMaybe [] $ Data.Map.lookup k mp

newloc :: CompilerMonad Loc
newloc = do
    (vrc, rlu, nextLoc, rspSize, strCodes) <- get
    put (vrc, rlu, nextLoc+1, rspSize, strCodes)
    return nextLoc

getNextStack :: CompilerMonad RegLoc
getNextStack = do
    (vrc, rlu, nextLoc, rspSize, strCodes) <- get
    put (vrc, rlu, nextLoc, rspSize+8, strCodes)
    return $ RSP rspSize

getFreeReg' :: Reg -> CompilerMonad Reg
getFreeReg' r = do
    if r > 9
        then throwError "unimplemented"
        else do
            (vrc, rlu, nextLoc, rspSize, strCodes) <- get
            case lookupArr (Reg r) rlu of
                [] -> return r
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

getIdentRegLoc :: BNFC'Position -> Ident -> CompilerMonad RegLoc
getIdentRegLoc pos ident = do
    (vrc, rlu, nextLoc, rspSize, strCodes) <- get
    case Data.Map.lookup ident vrc of
        Nothing -> throwError ("undefined variable " ++ show ident ++ " at " ++ show pos)
        Just regLoc -> return regLoc

getVarRegLoc :: Var -> CompilerMonad RegLoc
getVarRegLoc (IdentVar pos ident) = getIdentRegLoc pos ident
getVarRegLoc (ArrayVar pos arrVar expr) = throwError "unimplemented"
getVarRegLoc (AttrVar pos var attrIdent) = throwError "unimplemented"

compileIf :: Expr -> String -> String -> CompilerMonad StringBuilder -- TODO opt
compileIf (ELitTrue pos) lt lf = return $ BStr $ "\tjmp " ++ lt ++ "\n"
compileIf (ELitFalse pos) lt lf = return $ BStr $ "\tjmp " ++ lf ++ "\n"
compileIf (EVar pos var) lt lf = do
    valRef <- getRef pos ident
    return $ BLst [
        BStr "\tmov ", valRef, BStr ", %eax\n",
        BStr $ "\ttest %eax, %eax\n",
        BStr $ "\tjz " ++ lf ++ "\n",
        BStr $ "\tjmp " ++ lt ++ "\n"
        ]
compileIf (ENot pos expr) lt lf = compileExpr expr lf lt
compileIf (EOr pos expr0 expr1) lt lf = do
    lm <- genLabel
    code0 <- compileExpr expr0 lt lm
    code1 <- compileExpr expr1 lt lf
    return $ BLst [
        code0,
        BStr $ lm ++ ":\n",
        code1
        ]
compileIf (EAnd pos expr0 expr1) lt lf = do
    lm <- genLabel
    code0 <- compileExpr expr0 lm lf
    code1 <- compileExpr expr1 lt lf
    return $ BLst [
        code0,
        BStr $ lm ++ ":\n",
        code1
        ]
compileIf _ _ _ = throwError "expected bool"

compileExpr' :: Expr -> Reg -> CompilerMonad StringBuilder
compileExpr' (EVar pos var) r = do
    regLoc <- getVarRegLoc var
    case regLoc of
        Reg r -> return $ BLst []
        _ -> do
            return $ BStr $ "\tmov " ++ showRegLoc regLoc ++ ", " ++ showReg r ++ "\n"
compileExpr' (ELitInt pos n) r = do
    return $ BStr $ "\tmov $" ++ show n ++ ", " ++ showReg r ++ "\n"
compileExpr' (ELitTrue pos) r = compileExpr' (ELitInt pos 1) r
compileExpr' (ELitFalse pos) r = compileExpr' (ELitInt pos 0) r
compileExpr' (ELitNull pos classIdent) r = compileExpr' (ELitInt pos 0) r
compileExpr' (EString pos str) r = do
    (vrc, rlu, nextLoc, rspSize, (strCodes, strCodeNr)) <- get
    let strLabel = ".str_" ++ show strCodeNr
    let newStrCodes = BLst [
                strCodes,
                BStr $ strLabel ++ ": .ascii \"" ++ str ++ "\\0\"\n"
            ]
    put (vrc, rlu, nextLoc, rspSize, (newStrCodes, strCodeNr+1))
    return $ BStr $ "\tleaq " ++ strLabel ++  "(%rip), " ++ showReg r ++ "\n"
compileExpr' (EAdd pos expr0 op expr1) r = do
    -- TODO opt
    code1 <- compileExpr' expr0 r
    (code2, r2) <- compileExpr expr1
    case op of
        Plus _ -> return $ BStr $ "\tadd " ++ showReg r2 ++ ", " ++ showReg r ++ "\n"
        Minus _ -> return $ BStr $ "\tsub " ++ showReg r2 ++ ", " ++ showReg r ++ "\n"
compileExpr' (ERel pos expr0 op expr1) r = do
    -- TODO opt
    code1 <- compileExpr' expr0 r
    (code2, r2) <- compileExpr expr1
    let code3 = "\tcmp " ++ showReg r ++ ", " ++ showReg r2 ++ "\n"
    case op of
        LTH _ -> throwError "unimplemented"
        LE _ -> throwError "unimplemented"
        GTH _ -> throwError "unimplemented"
        GE _ -> throwError "unimplemented"
        EQU _ -> throwError "unimplemented"
        NE _ -> throwError "unimplemented"
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
compileExpr (EVar pos var) = do
    regLoc <- getVarRegLoc var
    case regLoc of
        Reg reg -> return (BLst [], reg)
        _ -> do
            reg <- getFreeReg
            return (BStr $ "\tmov " ++ showRegLoc regLoc ++ ", " ++ showReg reg ++ "\n", reg)
-- compileExpr (ELitInt pos n) = throwError "unimplemented" -- TODO opt
compileExpr (ELitTrue pos) = compileExpr (ELitInt pos 1)
compileExpr (ELitFalse pos) = compileExpr (ELitInt pos 0)
compileExpr (ELitArr pos elems) = throwError "unimplemented"
compileExpr (ELitNull pos classIdent) = compileExpr (ELitInt pos 0)
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
-- compileExpr (EString pos str) = 
compileExpr (Neg pos expr) = throwError "unimplemented"
compileExpr (Not pos expr) = throwError "unimplemented"
compileExpr (EMul pos expr0 op expr1) = do
    freeReg rax
    freeReg rdx -- freeReg probably does not work in nested expr
    code1 <- compileExpr' expr0 rax
    (code2, r2) <- compileExpr expr1
    case op of
        Times _ -> return (BStr $ "\timul " ++ showReg r2++ "\n", rax)
        Div _ -> return (BStr $ "\tidiv " ++ showReg r2 ++ "\n", rax)
        Mod _ -> return (BStr $ "\tidiv " ++ showReg r2 ++ "\n", rdx)
-- compileExpr (EAdd pos expr0 op expr1) = throwError "unimplemented"
-- compileExpr (ERel pos expr0 op expr1) = throwError "unimplemented"
compileExpr (EAnd pos expr0 expr1) = throwError "unimplemented"
compileExpr (EOr pos expr0 expr1) = throwError "unimplemented"
compileExpr expr = do
    r <- getFreeReg
    code <- compileExpr' expr r
    return (code, r)

compileStmt :: Stmt -> CompilerMonad StringBuilder
compileStmt (Empty pos) = return $ BLst []
compileStmt (BStmt pos (Block _bPos [])) = compileStmt (Empty pos)
compileStmt (BStmt pos (Block _bPos (stmt:stmts))) = do
    code1 <- compileStmt stmt
    code2 <- compileStmt (BStmt pos (Block _bPos stmts))
    return $ BLst [
            code1,
            code2
        ]
compileStmt (Decl pos tp []) = compileStmt (Empty pos)
compileStmt (Decl _pos tp (decl:decls)) = do
    case decl of
        NoInit pos ident -> do
            regLoc <- getNextStack -- TODO add using registers
            (vrc, rlu, nextLoc, rspSize, strCodes) <- get
            put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLoc, rspSize, strCodes) -- TODO check if [ident] is correct
            compileStmt (Empty pos)
        Init pos ident expr -> do
            regLoc <- getNextStack -- TODO add using registers
            (vrc, rlu, nextLoc, rspSize, strCodes) <- get
            put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLoc, rspSize, strCodes) -- TODO check if [ident] is correct
            (code, reg) <- compileExpr expr
            return $ BLst [
                    code,
                    BStr $ "\tmov " ++ showRegLoc (Reg reg) ++ ", " ++ showRegLoc regLoc ++ "\n"
                ]
compileStmt (Ass pos var expr) = do
    regLoc <- getVarRegLoc var
    case regLoc of
        RSP depth -> do
            (code, reg) <- compileExpr expr
            return $ BLst [
                    code,
                    BStr $ "\tmov " ++ showRegLoc (Reg reg) ++ ", " ++ showRegLoc regLoc ++ "\n"
                ]
        Reg reg -> compileExpr' expr reg
compileStmt (Incr pos var) = do
    regLoc <- getVarRegLoc var
    case regLoc of
        Reg reg -> return $ BStr $ "\tadd $1, " ++ showReg reg ++ "\n" 
        _ -> compileStmt (Ass pos var (EAdd pos (EVar pos var) (Plus pos) (ELitInt pos 1)))
compileStmt (Decr pos var) = do
    regLoc <- getVarRegLoc var
    case regLoc of
        Reg reg -> return $ BStr $ "\tsub $1, " ++ showReg reg ++ "\n" 
        _ -> compileStmt (Ass pos var (EAdd pos (EVar pos var) (Minus pos) (ELitInt pos 1)))
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

addArgs' :: [RegLoc] -> [Arg] -> CompilerMonad ()
addArgs' _ [] = return ()
addArgs' (regLoc:regLocs) ((Arg pos tp ident):args) = do
    (vrc, rlu, nextLoc, rspSize, strCodes) <- get
    case regLoc of
        Reg _ -> put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLoc, rspSize, strCodes)
        RSP rsp -> put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLoc, rsp+8, strCodes)

addArgs = addArgs' argRegLocs

compileTopDefs :: StringBuilder -> [TopDef] -> CompilerMonad StringBuilder
compileTopDefs code ((FnDef pos tp ident args block):lst) = do
    (vrc0, rlu0, nextLoc0, rspSizeOld0, strCodes0) <- get
    put (Data.Map.empty, Data.Map.empty, nextLoc0, 0, strCodes0)
    addArgs args
    currCode <- compileStmt (BStmt pos block)
    (vrc, rlu, nextLoc, rspSizeOld, strCodes) <- get
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
    (vrl, rlu, l, stackDepth, strCodes) <- get
    let (strCode, strNr) = strCodes
    return $ buildString (BLst [
        BStr $ ".data\n"
            ++ ".printInt: .ascii \"%d\\n\\0\"\n", -- TODO make it auto for all string 
        strCode,
        BStr $ ".text\n"
            ++ ".globl main\n",
        buildInCode,
        code
        ])