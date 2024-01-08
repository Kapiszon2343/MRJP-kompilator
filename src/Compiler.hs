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
type StackState = (Int, Int)
type CompilerStore = (VariableRegisterLoc, RegisterLocUse, Int, StackState, StringCodes)

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
showRegLoc (RSP n) = show n ++ "(%rsp)"

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

newLabel :: CompilerMonad String
newLabel = do
    (vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (vrc, rlu, nextLabel+1, stackState, strCodes)
    return $ "label_" ++ show nextLabel

getNextStack :: CompilerMonad RegLoc
getNextStack = do
    (vrc, rlu, nextLabel, (currStackSize, maxStackSize), strCodes) <- get
    put (vrc, rlu, nextLabel, (currStackSize+8, max maxStackSize $ currStackSize+8), strCodes)
    return $ RSP currStackSize

getFreeReg' :: Reg -> CompilerMonad Reg
getFreeReg' r = do
    if r > 9
        then throwError "unimplemented"
        else do
            (vrc, rlu, nextLabel, stackState, strCodes) <- get
            case lookupArr (Reg r) rlu of
                [] -> return r
                _ -> getFreeReg' (r+1)

getFreeReg :: CompilerMonad Reg
getFreeReg = getFreeReg' (rax+2)

getFreeRegLoc :: CompilerMonad RegLoc
getFreeRegLoc = do
    -- TODO add registers
    getNextStack

releaseReg :: Reg -> CompilerMonad ()
releaseReg reg = do
    (vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (vrc, Data.Map.insert (Reg reg) [] rlu, nextLabel, stackState, strCodes)

freeReg :: Reg -> CompilerMonad StringBuilder
freeReg r = do
    -- TODO actually free register
    return $ BStr ""

freeRegLoc :: RegLoc -> CompilerMonad StringBuilder
freeRegLoc r = do
    -- TODO actually free register
    return $ BStr ""

getIdentRegLoc :: BNFC'Position -> Ident -> CompilerMonad RegLoc
getIdentRegLoc pos ident = do
    (vrc, rlu, nextLabel, stackState, strCodes) <- get
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
    regLoc <- getVarRegLoc var
    return $ BLst [
        BStr $ "\tmov " ++ showRegLoc regLoc ++ ", %rax\n",
        BStr  "\ttest %rax, %rax\n",
        BStr $ "\tjz " ++ lf ++ "\n",
        BStr $ "\tjmp " ++ lt ++ "\n"
        ]
compileIf (ENot pos expr) lt lf = compileIf expr lf lt
compileIf (EOr pos expr0 expr1) lt lf = do
    lm <- newLabel
    code0 <- compileIf expr0 lt lm
    code1 <- compileIf expr1 lt lf
    return $ BLst [
        code0,
        BStr $ lm ++ ":\n",
        code1
        ]
compileIf (EAnd pos expr0 expr1) lt lf = do
    lm <- newLabel
    code0 <- compileIf expr0 lm lf
    code1 <- compileIf expr1 lt lf
    return $ BLst [
        code0,
        BStr $ lm ++ ":\n",
        code1
        ]
compileIf (ERel pos expr0 op expr1) lt lf = do
    (code1, r1) <- compileExpr expr0
    (code2, r2) <- compileExpr expr1
    let codeCmp = case (r1, r2) of
            (Reg _, _) -> BStr $ "\tcmp " ++ showRegLoc r2 ++ ", " ++ showRegLoc r1 ++ "\n"
            (_, Reg _) -> BStr $ "\tcmp " ++ showRegLoc r2 ++ ", " ++ showRegLoc r1 ++ "\n"
            _ -> BLst [
                    BStr $ "\tmov " ++ showRegLoc r2 ++ ", " ++ showReg rax ++ "\n",
                    BStr $ "\tcmp " ++ showReg rax ++ ", " ++ showRegLoc r1 ++ "\n"
                ]
    let codeJmpTrue = case op of
            LTH _ -> BStr $ "\tjl " ++ lt ++ "\n"
            LE _ -> BStr $ "\tjle " ++ lt ++ "\n"
            GTH _ -> BStr $ "\tjg " ++ lt ++ "\n"
            GE _ -> BStr $ "\tjge " ++ lt ++ "\n"
            EQU _ -> BStr $ "\tje " ++ lt ++ "\n"
            NE _ -> BStr $ "\tjne " ++ lt ++ "\n"
    return $ BLst [
            code1,
            code2,
            codeCmp,
            codeJmpTrue,
            BStr $ "\tjmp " ++ lf ++ "\n"
        ]
compileIf expr lt lf = do
    (code, regLoc) <- compileExpr expr
    return $ BLst [
        code,
        BStr $ "\tmov " ++ showRegLoc regLoc ++ ", %rax\n",
        BStr  "\ttest %rax, %rax\n",
        BStr $ "\tjz " ++ lf ++ "\n",
        BStr $ "\tjmp " ++ lt ++ "\n"
        ]

compileExpr' :: Expr -> RegLoc -> CompilerMonad StringBuilder
compileExpr' (EVar pos var) r = do
    regLoc <- getVarRegLoc var
    if r == regLoc
        then return $ BLst []
        else case (r, regLoc) of
            (Reg _, _) -> return $ BStr $ "\tmov " ++ showRegLoc regLoc ++ ", " ++ showRegLoc r ++ "\n"
            (_, Reg _) -> return $ BStr $ "\tmov " ++ showRegLoc regLoc ++ ", " ++ showRegLoc r ++ "\n"
            _ -> return $ BLst [
                    BStr $ "\tmov " ++ showRegLoc regLoc ++ ", " ++ showReg rax ++ "\n",
                    BStr $ "\tmov " ++ showReg rax ++ ", " ++ showRegLoc r ++ "\n"
                ]
compileExpr' (ELitInt pos n) r = do
    case r of 
        Reg _ -> return $ BStr $ "\tmov $" ++ show n ++ ", " ++ showRegLoc r ++ "\n"
        _ -> return $ BLst [
                BStr $ "\tmov $" ++ show n ++ ", " ++ showReg rax ++ "\n", 
                BStr $ "\tmov " ++ showReg rax ++ ", " ++ showRegLoc r ++ "\n"
            ]
compileExpr' (ELitTrue pos) r = compileExpr' (ELitInt pos 1) r
compileExpr' (ELitFalse pos) r = compileExpr' (ELitInt pos 0) r
compileExpr' (ELitNull pos classIdent) r = compileExpr' (ELitInt pos 0) r
compileExpr' (EString pos str) r = do
    (vrc, rlu, nextLabel, stackState, (strCodes, strCodeNr)) <- get
    let strLabel = ".str_" ++ show strCodeNr
    let newStrCodes = BLst [
                strCodes,
                BStr $ strLabel ++ ": .ascii \"" ++ str ++ "\\n\\0\"\n"
            ]
    put (vrc, rlu, nextLabel, stackState, (newStrCodes, strCodeNr+1))
    case r of
        Reg _ -> return $ BStr $ "\tlea " ++ strLabel ++  "(%rip), " ++ showRegLoc r ++ "\n"
        _ -> return $ BLst [
                BStr $ "\tlea " ++ strLabel ++  "(%rip), " ++ showReg rax ++ "\n",
                BStr $ "\tmov " ++ showReg rax ++  ", " ++ showRegLoc r ++ "\n"
            ]
compileExpr' (EAdd pos expr0 op expr1) r = do
    -- TODO opt
    code1 <- compileExpr' expr0 r
    (code2, r2) <- compileExpr expr1
    let isReg = case (r, r2) of
            (Reg _, _) -> True
            (_, Reg _) -> True
            _ -> False
    let codeAdd = case (isReg, op) of
            (True, Plus _) -> BStr $ "\tadd " ++ showRegLoc r2 ++ ", " ++ showRegLoc r ++ "\n"
            (False, Plus _) -> BLst [
                    BStr $ "\tmov " ++ showRegLoc r2 ++ ", " ++ showReg rax ++ "\n",
                    BStr $ "\tadd " ++ showReg rax ++ ", " ++ showRegLoc r ++ "\n"
                ]
            (True, Minus _) -> BStr $ "\tsub " ++ showRegLoc r2 ++ ", " ++ showRegLoc r ++ "\n"
            (False, Minus _) -> BLst [
                    BStr $ "\tmov " ++ showRegLoc r2 ++ ", " ++ showReg rax ++ "\n",
                    BStr $ "\tsub " ++ showReg rax ++ ", " ++ showRegLoc r ++ "\n"
                ]
    return $ BLst [
            code2,
            code1,
            codeAdd
        ]
compileExpr' (ERel pos expr0 op expr1) r = do
    lt <- newLabel
    lf <- newLabel
    ln <- newLabel
    codeIf <- compileIf (ERel pos expr0 op expr1) lt lf
    return $ BLst [
            codeIf,
            BStr $ lt ++ ":\n",
            BStr $ "\tmov $1, " ++ showRegLoc r ++ "\n",
            BStr $ "\tjmp " ++ ln ++ "\n",
            BStr $ lf ++ ":\n",
            BStr $ "\tmov $0, " ++ showRegLoc r ++ "\n",
            BStr $ ln ++ ":\n"
        ]
compileExpr' (EAnd pos expr0 expr1) r = do
    lt <- newLabel
    lf <- newLabel
    ln <- newLabel
    codeIf <- compileIf (EAnd pos expr0 expr1) lt lf
    return $ BLst [
            codeIf,
            BStr $ lt ++ ":\n",
            BStr $ "\tmov $1, " ++ showRegLoc r ++ "\n",
            BStr $ "\tjmp " ++ ln ++ "\n",
            BStr $ lf ++ ":\n",
            BStr $ "\tmov $0, " ++ showRegLoc r ++ "\n",
            BStr $ ln ++ ":\n"
        ]
compileExpr' (EOr pos expr0 expr1) r = do
    lt <- newLabel
    lf <- newLabel
    ln <- newLabel
    codeIf <- compileIf (EOr pos expr0 expr1) lt lf
    return $ BLst [
            codeIf,
            BStr $ lt ++ ":\n",
            BStr $ "\tmov $1, " ++ showRegLoc r ++ "\n",
            BStr $ "\tjmp " ++ ln ++ "\n",
            BStr $ lf ++ ":\n",
            BStr $ "\tmov $0, " ++ showRegLoc r ++ "\n",
            BStr $ ln ++ ":\n"
        ]
compileExpr' expr r = do
    (code, rr) <- compileExpr expr
    let codeMov = case (rr, r) of
            (Reg _, _) -> BStr $ "\tmov " ++ showRegLoc rr ++ ", " ++ showRegLoc r ++ "\n" 
            (_, Reg _) -> BStr $ "\tmov " ++ showRegLoc rr ++ ", " ++ showRegLoc r ++ "\n" 
            _ -> BLst [
                    BStr $ "\tmov " ++ showRegLoc rr ++ ", " ++ showReg rax ++ "\n" ,
                    BStr $ "\tmov " ++ showReg rax ++ ", " ++ showRegLoc r ++ "\n" 
                ]
    return $ BLst [
            code,
            codeMov
        ]

fillArgs :: [RegLoc] -> [Expr] -> CompilerMonad StringBuilder
fillArgs (regLoc:regLocs) (expr:exprs) = do
    freeRegLoc regLoc
    exprCode <- compileExpr' expr regLoc
    tailCode <- fillArgs regLocs exprs
    return $ BLst [
            exprCode,
            tailCode
        ]
fillArgs regLocs [] = return $ BLst []

compileExpr :: Expr -> CompilerMonad (StringBuilder, RegLoc)
compileExpr (ENew pos newVar) = throwError "unimplemented"
compileExpr (EVar pos var) = do
    regLoc <- getVarRegLoc var
    return (BLst [], regLoc)
-- compileExpr (ELitInt pos n) = throwError "unimplemented" -- TODO opt
compileExpr (ELitTrue pos) = compileExpr (ELitInt pos 1)
compileExpr (ELitFalse pos) = compileExpr (ELitInt pos 0)
compileExpr (ELitArr pos elems) = throwError "unimplemented"
compileExpr (ELitNull pos classIdent) = compileExpr (ELitInt pos 0)
compileExpr (EApp pos var exprs) = do
    fillCode <- fillArgs argRegLocs exprs
    return (
            BLst [
                fillCode,
                BStr $ "\tcall " ++ showVar var ++ "\n" -- TODO Maybe check for arrays
            ],
            Reg rax
        )
-- compileExpr (EString pos str) = 
compileExpr (ENeg pos expr) = do
    (code, r) <- compileExpr expr
    return (BLst [
            code,
            BStr  "\txorq %rax, %rax\n",
            BStr $ "\tsub " ++ showRegLoc r ++ ", %rax\n",
            BStr $ "\tmov %rax, " ++ showRegLoc r ++ "\n"
        ], r)
compileExpr (ENot pos expr) = do
    (code, r) <- compileExpr expr
    return (BLst [
            code,
            BStr $ "\txorq $1, " ++ showRegLoc r ++ "\n"
        ]
        ,r)
compileExpr (EMul pos expr0 op expr1) = do
    (code1, r1) <- compileExpr expr0
    (code2, r2) <- compileExpr expr1
    let (codeMul, outReg) = case op of
            Times _ -> (BStr $ "\timulq " ++ showRegLoc r2 ++ "\n", rax)
            Div _ -> (BStr $ "\tidivq " ++ showRegLoc r2 ++ "\n", rax)
            Mod _ -> (BStr $ "\tidivq " ++ showRegLoc r2 ++ "\n", rdx)
    return (BLst [
            code1,
            code2,
            BStr $ "\tmov " ++ showRegLoc r1 ++ ", %rax\n",
            codeMul
        ], Reg outReg)
-- compileExpr (EAdd pos expr0 op expr1) = throwError "unimplemented"
-- compileExpr (ERel pos expr0 op expr1) = throwError "unimplemented"
-- compileExpr (EAnd pos expr0 expr1) = throwError "unimplemented"
-- compileExpr (EOr pos expr0 expr1) = throwError "unimplemented"
compileExpr expr = do
    r <- getFreeRegLoc
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
    codeHead <- case decl of
        NoInit pos ident -> do
            regLoc <- getNextStack -- TODO add using registers
            (vrc, rlu, nextLabel, stackState, strCodes) <- get
            put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLabel, stackState, strCodes) -- TODO check if [ident] is correct
            compileStmt (Empty pos)
        Init pos ident expr -> do
            regLoc <- getNextStack -- TODO add using registers
            (vrc, rlu, nextLabel, stackState, strCodes) <- get
            put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLabel, stackState, strCodes) -- TODO check if [ident] is correct
            compileExpr' expr regLoc
    codeTail <- compileStmt (Decl _pos tp decls)
    return $ BLst [codeHead, codeTail]
compileStmt (Ass pos var expr) = do
    regLoc <- getVarRegLoc var
    (codeExpr, r) <- compileExpr expr
    let codeSet = case (regLoc, r) of
            (Reg _, _) -> BStr $ "mov " ++ showRegLoc r ++ ", " ++ showRegLoc regLoc ++ "\n"
            (_, Reg _) -> BStr $ "mov " ++ showRegLoc r ++ ", " ++ showRegLoc regLoc ++ "\n"
            _ -> BLst [
                    BStr $ "mov " ++ showRegLoc r ++ ", " ++ showReg rax ++ "\n",
                    BStr $ "mov " ++ showReg rax ++ ", " ++ showRegLoc regLoc ++ "\n"
                ]
    return $ BLst [
            codeExpr,
            codeSet
        ]
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
    code <- compileExpr' expr (Reg rax)
    return $ BLst [
            code,
            BFil filRetN
        ]
compileStmt (VRet pos) = return $ BFil filRetN
compileStmt (Cond pos expr stmt) = do
    labelTrue <- newLabel
    labelExit <- newLabel
    codeCond <- compileIf expr labelTrue labelExit
    codeTrue <- compileStmt stmt
    return $ BLst [
            codeCond,
            BStr $ labelTrue ++ ":\n",
            codeTrue,
            BStr $ labelExit ++ ":\n"
        ]
compileStmt (CondElse pos expr stmtTrue stmtFalse) = do
    labelTrue <- newLabel
    labelFalse <- newLabel
    labelExit <- newLabel
    codeCond <- compileIf expr labelTrue labelFalse
    codeTrue <- compileStmt stmtTrue
    codeFalse <- compileStmt stmtFalse
    return $ BLst [
            codeCond,
            BStr $ labelTrue ++ ":\n",
            codeTrue,
            BStr $ "\tjmp " ++ labelExit ++ "\n",
            BStr $ labelFalse ++ ":\n",
            codeFalse,
            BStr $ labelExit ++ ":\n"
        ]
compileStmt (While pos expr stmt) = do
    labelLoop <- newLabel
    labelExit <- newLabel
    codeCond <- compileIf expr labelLoop labelExit
    codeLoop <- compileStmt stmt
    return $ BLst [
            BStr $ labelLoop ++ ":\n",
            codeLoop,
            codeCond,
            BStr $ labelExit ++ ":\n"
        ]
compileStmt (For pos incrTp incrIdent incrSet cond incrStmt blockStmt) = throwError "unimplemented"
compileStmt (ForEach pos elemTp elemIdent arrExpr blockStmt) = throwError "unimplemented"
compileStmt (SExp pos expr) = do
    (code, _r) <- compileExpr expr
    return code

addArgs' :: [RegLoc] -> [Arg] -> CompilerMonad ()
addArgs' _ [] = return ()
addArgs' (regLoc:regLocs) ((Arg pos tp ident):args) = do
    (vrc, rlu, nextLabel, (currStack, maxStack), strCodes) <- get
    case regLoc of
        Reg _ -> put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLabel, (currStack, maxStack), strCodes)
        RSP rsp -> put (Data.Map.insert ident regLoc vrc, Data.Map.insert regLoc [ident] rlu, nextLabel, (rsp+8, max rsp maxStack), strCodes)
    addArgs' regLocs args

addArgs = addArgs' argRegLocs

compileTopDefs :: StringBuilder -> [TopDef] -> CompilerMonad StringBuilder
compileTopDefs code ((FnDef pos tp ident args block):lst) = do
    (vrc0, rlu0, nextLabel0, stackStateOld0, strCodes0) <- get
    put (Data.Map.empty, Data.Map.empty, nextLabel0, (0, 0), strCodes0)
    addArgs args
    currCode <- compileStmt (BStmt pos block)
    (vrc, rlu, nextLabel, (oldStack, oldStackMax), strCodes) <- get
    let stackMax = 32 * div (oldStackMax + 31) 32
    compileTopDefs (BLst [
            code,
            BStr $ showIdent ident ++ ":\n"
                ++ "\tpush %rbp\n"
                ++ "\tmov %rsp, %rbp\n"
                ++ "\tsub $" ++ show stackMax ++ ", %rsp\n",
            fillStringBuilder (Data.Map.singleton filRetN (
                   "\tadd $" ++ show stackMax ++ ", %rsp\n"
                ++ "\tmov %rbp, %rsp\n"
                ++ "\tpop %rbp\n"
                ++ "\tret\n")) currCode
        ]) lst
compileTopDefs code ((ClassDef pos ident elems):lst) = throwError "unimplemented"
compileTopDefs code ((ClassExt pos classIdent parentIdent elems):lst) = throwError "unimplemented"
compileTopDefs code [] = do return code

compileBuiltInFunctions :: [BuiltInFunction] -> CompilerMonad (StringBuilder, StringBuilder)
compileBuiltInFunctions [] = return $ (BLst [], BLst [])
compileBuiltInFunctions ((_,_,code1,codeData1):tail) = do
    (code2, codeData2) <- compileBuiltInFunctions tail
    return (BLst [
            code1,
            code2
        ], BLst [
            codeData1,
            codeData2
        ])

filRetN = 1

compileProgram :: Program -> CompilerMonad String
compileProgram (Program pos topDefs) = do
    (buildInCode, builtInData) <- compileBuiltInFunctions builtInFunctions
    code <- compileTopDefs (BLst []) topDefs
    (vrl, rlu, l, stackDepth, strCodes) <- get
    let (strCode, strNr) = strCodes
    return $ buildString (BLst [
        BStr ".data\n",
        builtInData,
        strCode,
        BStr $ ".text\n"
            ++ ".globl main\n",
        buildInCode,
        code
        ])