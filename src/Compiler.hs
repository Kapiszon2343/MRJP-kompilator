{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use foldr" #-}
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
import InfoDigger (digStmtInfoPub)
import Control.Exception.Base (throw)

instance Ord RegLoc where
    compare (Reg r0) (Reg r1) = compare r0 r1
    compare (RBP r0) (RBP r1) = compare r1 r0
    compare (Lit n0) (Lit n1) = compare n0 n1
    compare (Mem _ ref2 _ _) (Mem _ ref1 _ _) = compare ref1 ref2
    compare (Lit _) _ = LT
    compare _ (Lit _) = GT
    compare (Reg _) _ = LT
    compare _ (Reg _) = GT
    compare (RBP _) _ = LT
    compare _ (RBP _) = GT
type VariableRegisterLoc = Data.Map.Map Loc RegLoc 
data LocUse = IdentUse Ident
    | TMPUse
type RegisterLocUse = Data.Map.Map RegLoc [LocUse]
type StringCodes = (StringBuilder, Int)
type StackState = (Int, Int)
type LocTypes = (Data.Map.Map Loc Type, Int)
type CompilerStore = (LocTypes, VariableRegisterLoc, RegisterLocUse, Int, StackState, StringCodes)

type VarVal = Integer

type CompilerMonad = ExceptT String (ReaderT Env (StateT CompilerStore IO))

type Ret = (Env -> Env, VarVal)

stableRegs = [10..15]
allRegs = [rax..15] -- TODO all registers
argRegLocs :: Int -> [RegLoc]
argRegLocs = argRegLocs' argReg

argRegLocs' :: [Reg] -> Int -> [RegLoc]
argRegLocs' _ 0 = []
argRegLocs' [] remainingArgs = argRegLocs'' ((-8) * remainingArgs - 8)
argRegLocs' (reg:regs) remainingArgs = Reg reg:argRegLocs' regs (remainingArgs-1)

argRegLocs'' :: Int -> [RegLoc]
argRegLocs'' 0 = []
argRegLocs'' stackDist = RBP stackDist:argRegLocs'' (stackDist+8)

lookupInt :: Ord k => k -> Data.Map.Map k Int -> Int
lookupInt k mp = fromMaybe 0 $ Data.Map.lookup k mp

lookupArr k mp = fromMaybe [] $ Data.Map.lookup k mp

newLoc :: CompilerMonad Loc
newLoc = do
    ((mp, l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put ((mp, l+1), vrc, rlu, nextLabel, stackState, strCodes)
    return l

getIdentLoc :: BNFC'Position -> Ident -> CompilerMonad Loc 
getIdentLoc pos ident = do 
    (locs, _) <- ask
    case Data.Map.lookup ident locs of
        Nothing -> throwError $ "undefined variable at " ++ showPos pos
        Just ret -> return ret

insertLocTp :: Loc -> Type -> CompilerMonad ()
insertLocTp loc tp = do
    ((lt,l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put ((Data.Map.insert loc tp lt,l), vrc, rlu, nextLabel, stackState, strCodes)

getVarType :: Var -> CompilerMonad Type
getVarType (IdentVar pos ident) = do
    loc <- getIdentLoc pos ident
    ((lt,l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    case Data.Map.lookup loc lt of
        Nothing -> throwError $ "undefined variable at " ++ showPos pos
        Just ret -> return ret
getVarType (ArrayVar pos var expr) = do
    arrMTp <- getVarType var
    case arrMTp of
        (Array _ inTp) -> return inTp
        _ -> throwError $ "Expected " ++ showVar var ++ " to be an array, got: " ++ showType arrMTp
getVarType (AttrVar pos var ident) = do
    baseTp <- getVarType var
    case baseTp of
        Array _ _ -> if showIdent ident == "length"
            then return $ Int pos
            else throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ " does not have attribute " ++ showIdent ident
        Class _ classIdent -> do
            (_, envClass) <- ask
            let classForm = Data.Map.lookup classIdent envClass
            case classForm of
                Just ((attrMap, _),_) -> do
                    let attr = Data.Map.lookup ident attrMap
                    case attr of
                        Just (tp, _) -> return tp
                        Nothing -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ " does not have attribute " ++ showIdent ident
                Nothing -> throwError $ "Something went horribly wrong!!\n Could not find class " ++ showIdent classIdent ++ "of variable " ++ showVar var ++ " at: " ++ showPos pos
        _ -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ "does not have attributes"

newLabel :: CompilerMonad String
newLabel = do
    (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (lt, vrc, rlu, nextLabel+1, stackState, strCodes)
    return $ "label_" ++ show nextLabel

getNextStack' :: Int -> CompilerMonad RegLoc
getNextStack' stackSize = do
    (lt, vrc, rlu, nextLabel,  (currStackSize, maxStackSize), strCodes) <- get
    case lookupArr (RBP stackSize) rlu of
        [] -> do
            put (lt, vrc, Data.Map.insert (RBP stackSize) [TMPUse] rlu, nextLabel, (stackSize, max maxStackSize stackSize), strCodes)
            return $ RBP stackSize
        _ -> getNextStack' $ stackSize + 8

getNextStack :: CompilerMonad RegLoc
getNextStack = getNextStack' 8

getFreeReg' :: Reg -> CompilerMonad Reg
getFreeReg' r = do
    if r > 15
        then throwError "unimplemented"
        else do
            (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
            case lookupArr (Reg r) rlu of
                [] -> return r
                _ -> getFreeReg' (r+1)

getFreeReg :: CompilerMonad Reg
getFreeReg = getFreeReg' (rax+1)

getFreeRegLoc :: CompilerMonad RegLoc
getFreeRegLoc = do
    -- TODO add registers
    getNextStack

releaseReg :: Reg -> CompilerMonad ()
releaseReg reg = do
    (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (lt, vrc, Data.Map.insert (Reg reg) [] rlu, nextLabel, stackState, strCodes)

freeReg :: Reg -> CompilerMonad StringBuilder
freeReg r = do
    (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
    case Data.Map.lookup (Reg r) rlu of
        Nothing -> return $ BLst []
        Just [] -> return $ BLst []
        Just ref -> do
            newRegLoc <- getFreeRegLoc
            (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
            let rlu1 = Data.Map.insert (Reg r) [] rlu
            let rlu2 = Data.Map.insert newRegLoc ref rlu1
            put (lt, vrc, rlu2, nextLabel, stackState, strCodes)
            return $ moveRegsLocs (Reg r) newRegLoc

freeRegLoc :: RegLoc -> CompilerMonad StringBuilder
freeRegLoc r = do
    case r of 
        Reg rr -> freeReg rr
        _ -> do
            (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
            case Data.Map.lookup r rlu of
                Nothing -> return $ BLst []
                Just [] -> return $ BLst []
                Just ref -> do
                    newRegLoc <- getFreeRegLoc
                    (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
                    let rlu1 = Data.Map.insert r [] rlu
                    let rlu2 = Data.Map.insert newRegLoc ref rlu1
                    put (lt, vrc, rlu2, nextLabel, stackState, strCodes)
                    return $ moveRegsLocs r newRegLoc

getIdentRegLoc :: BNFC'Position -> Ident -> CompilerMonad RegLoc
getIdentRegLoc pos ident = do
    (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
    loc <- getIdentLoc pos ident
    case Data.Map.lookup loc vrc of
        Nothing -> throwError ("undefined variable " ++ show ident ++ " at " ++ show pos)
        Just regLoc -> return regLoc

getVarRegLoc :: Var -> CompilerMonad (StringBuilder, RegLoc)
getVarRegLoc (IdentVar pos ident) = do
    regLoc <- getIdentRegLoc pos ident
    return (BLst [], regLoc)
getVarRegLoc (ArrayVar pos arrVar expr) = do
    (codeVar, regVar) <- getVarRegLoc arrVar
    (codeIdx, regIdx) <- compileExpr expr
    return (BLst [codeVar, codeIdx], Mem 16 regVar regIdx 8)
getVarRegLoc (AttrVar pos var attrIdent) = throwError "unimplemented"

maybeMoveReg' :: [Reg] -> RegLoc -> CompilerMonad (StringBuilder, RegLoc)
maybeMoveReg' [] reg = return (BLst [], reg)
maybeMoveReg' (reg:regs) regLoc = if regLoc == Reg reg
    then do
        newRegLoc <- getFreeRegLoc
        return (moveRegsLocs regLoc newRegLoc, newRegLoc)
    else maybeMoveReg' regs regLoc

maybeMoveReg :: RegLoc -> CompilerMonad (StringBuilder, RegLoc)
maybeMoveReg = maybeMoveReg' (rax:argReg)

calcExprType :: Expr -> CompilerMonad Type
calcExprType (ENew pos new) =
    case new of
        NewBase pos tp -> return tp
        NewArray pos newTp expr -> do
            arrTp <- calcExprType (ENew pos newTp)
            return (Array pos arrTp) 
calcExprType (EVar pos var) = getVarType var
calcExprType (ELitInt pos n) = return $ Int pos
calcExprType (ELitTrue pos) = return $ Bool pos
calcExprType (ELitFalse pos) = return $ Bool pos
calcExprType (ELitArr pos []) = return $ Array pos $ Class pos $ Ident "Object"
calcExprType (ELitArr pos (expr:exprs)) = do
    tp <- calcExprType expr
    return $ Array pos tp
calcExprType (ELitNull pos ident) = return $ Class pos $ Ident "Object"
calcExprType (EApp pos var exprs) = do
    tp <- getVarType var
    case tp of
        Fun p retTp _ -> return retTp
        _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected function\nActual: " ++ showType tp
calcExprType (EString pos str) = return $ Str pos
calcExprType (ENeg pos expr) = return $ Int pos
calcExprType (ENot pos expr) = return $ Bool pos
calcExprType (EMul pos expr1 op expr2) = return $ Int pos
calcExprType (EAdd pos expr1 op expr2) = calcExprType expr1
calcExprType (ERel pos expr1 op expr2) = return $ Bool pos
calcExprType (EAnd pos expr1 expr2) = return $ Bool pos
calcExprType (EOr pos expr1 expr2) = return $ Bool pos

compileIf :: Expr -> String -> String -> CompilerMonad StringBuilder -- TODO opt
compileIf (ELitTrue pos) lt lf = return $ BStr $ "\tjmp " ++ lt ++ "\n"
compileIf (ELitFalse pos) lt lf = return $ BStr $ "\tjmp " ++ lf ++ "\n"
compileIf (EVar pos var) lt lf = do
    (getCode, regLoc) <- getVarRegLoc var
    return $ BLst [
        getCode,
        moveRegsLocs regLoc (Reg rax),
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
    (code1, r1') <- compileExpr expr0
    (codeMoveR1, r1) <- maybeMoveReg r1'
    (code2, r2) <- compileExpr expr1
    let tmpReg = if r2 == Reg rax
        then argRegLoc1
        else Reg rax
    let codeCmp = case (r1, r2) of
            (Lit n1, _) -> BLst [ -- TODO OPT
                    moveRegsLocs r1 tmpReg,
                    BStr $ "\tcmpq " ++ showRegLoc r2 ++ ", " ++ showRegLoc tmpReg ++ "\n"
                ]
            (Reg _, _) -> BStr $ "\tcmpq " ++ showRegLoc r2 ++ ", " ++ showRegLoc r1 ++ "\n"
            (_, Reg _) -> BStr $ "\tcmpq " ++ showRegLoc r2 ++ ", " ++ showRegLoc r1 ++ "\n"
            _ -> BLst [
                    moveRegsLocs r1 tmpReg,
                    BStr $ "\tcmpq " ++ showRegLoc r2 ++ ", " ++ showRegLoc tmpReg ++ "\n"
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
            codeMoveR1,
            code2,
            codeCmp,
            codeJmpTrue,
            BStr $ "\tjmp " ++ lf ++ "\n"
        ]
compileIf expr lt lf = do
    (code, regLoc) <- compileExpr expr
    return $ BLst [
        code,
        moveRegsLocs regLoc (Reg rax),
        BStr  "\ttest %rax, %rax\n",
        BStr $ "\tjz " ++ lf ++ "\n",
        BStr $ "\tjmp " ++ lt ++ "\n"
        ]

compileExpr' :: Expr -> RegLoc -> CompilerMonad StringBuilder
compileExpr' (ENew pos newVar) r = do
    case newVar of
        NewBase newPos tp -> case tp of
            Class tpPos classIdent -> throwError "unimplemented"
            Str tpPos -> return $ BLst [
                    moveRegsLocs (Lit 1) argRegLoc0,
                    BStr   "\tcall malloc\n",
                    moveRegsLocs (Lit 0) (Mem 0 (Reg rax) (Lit 0) 0),
                    moveRegsLocs (Reg rax) r
                ]
            _ -> compileExpr' (ELitInt pos 0) r
        NewArray newPos internalNew expr -> do
            let (reg, freeCode2, restoreCode2) = case r of
                    Reg _ -> (r, BLst[], BLst[])
                    _ -> (argRegLoc2, 
                        BStr $ "\tpush " ++ showRegLoc argRegLoc2 ++ "\n",
                        BStr $ "\tpop " ++ showRegLoc argRegLoc2 ++ "\n")
            let freeCode1 = BStr $ "\tpush " ++ showRegLoc argRegLoc1 ++ "\n"
            let restoreCode1 = BStr $ "\tpop " ++ showRegLoc argRegLoc1 ++ "\n"
            let freeCode0 = BStr $ "\tpush " ++ showRegLoc argRegLoc0 ++ "\n"
            let restoreCode0 = BStr $ "\tpop " ++ showRegLoc argRegLoc0 ++ "\n"
            exprCode <- compileExpr' expr argRegLoc1
            loopLabel <- newLabel
            internalNewCode <- compileExpr' (ENew pos internalNew) (Mem 16 reg argRegLoc1 8)
            return $ BLst [
                    freeCode0,
                    freeCode1,
                    freeCode2,
                    exprCode,
                    moveRegsLocs argRegLoc1 argRegLoc0,
                    BStr $ "\tadd $2, " ++ showRegLoc argRegLoc0 ++ "\n",
                    BStr $ "\tshl $3, " ++ showRegLoc argRegLoc0 ++ "\n",
                    BStr   "\tcall malloc\n",
                    moveRegsLocs argRegLoc1 (Mem 8 (Reg rax) (Lit 0) 0),
                    moveRegsLocs (Reg rax) reg,
                    BStr $ loopLabel ++ ":\n",
                    BStr $ "\tdecq " ++ showRegLoc argRegLoc1 ++ "\n",
                    internalNewCode,
                    BStr $ "\ttest " ++ showRegLoc argRegLoc1 ++ ", " ++ showRegLoc argRegLoc1 ++ "\n",
                    BStr $ "\tjnz " ++ loopLabel ++ "\n",
                    moveRegsLocs reg (Reg rax),
                    restoreCode2,
                    restoreCode1,
                    restoreCode0,
                    moveRegsLocs (Reg rax) r
                ]
compileExpr' (EString pos str) r = do
    (lt, vrc, rlu, nextLabel, stackState, (strCodes, strCodeNr)) <- get
    let strLabel = ".str_" ++ show strCodeNr
    let newStrCodes = BLst [
                strCodes,
                BStr $ strLabel ++ ": .ascii \"" ++ str ++ "\\0\"\n"
            ]
    put (lt, vrc, rlu, nextLabel, stackState, (newStrCodes, strCodeNr+1))
    case r of
        Reg _ -> return $ BStr $ "\tlea " ++ strLabel ++  "(%rip), " ++ showRegLoc r ++ "\n"
        _ -> return $ BLst [
                BStr $ "\tlea " ++ strLabel ++  "(%rip), " ++ showReg rax ++ "\n",
                BStr $ "\tmovq " ++ showReg rax ++  ", " ++ showRegLoc r ++ "\n"
            ]
compileExpr' (EAdd pos expr0 op expr1) r = do
    tp <- calcExprType expr0
    case tp of
        Str _ -> do 
            code1 <- compileExpr' expr0 r
            (code15, r15) <- maybeMoveReg r
            (code2, r2) <- compileExpr expr1
            loopCond1 <- newLabel
            loopStart1 <- newLabel
            loopCond2 <- newLabel
            loopStart2 <- newLabel
            loopCond3 <- newLabel
            loopStart3 <- newLabel
            loopCond4 <- newLabel
            loopStart4 <- newLabel
            let (tmpReg1, tmpReg2) = if r15 == Reg rax || r2 == Reg rdx
                then (Reg rdx, Reg rax)
                else (Reg rax, Reg rdx)
            return $ BLst [
                        code1,
                        code15,
                        code2,
                        moveRegsLocs r2 tmpReg2,
                        moveRegsLocs r15 tmpReg1,
                        BStr $ "\tpush " ++ showRegLoc argRegLoc0 ++ "\n",
                        BStr   "\tpush %r12\n",
                        BStr   "\tpush %r13\n",

                        moveRegsLocs tmpReg1 (Reg 12),
                        moveRegsLocs tmpReg2 (Reg 13),
                        moveRegsLocs (Lit 1) argRegLoc0,

                        BStr $ "\tjmp " ++ loopCond1 ++ "\n",
                        BStr $ loopStart1 ++ ":\n",
                        BStr $ "\tadd $1, " ++ showRegLoc argRegLoc0 ++ "\n",
                        BStr   "\tadd $1, %rax\n",
                        BStr $ loopCond1 ++ ":\n",
                        BStr   "\tmovb 0(%rax), %dl\n",
                        BStr   "\ttest %dl, %dl\n",
                        BStr $ "\tjnz " ++ loopStart1 ++ "\n",
                        
                        moveRegsLocs (Reg 13) (Reg rax),
                        BStr $ "\tjmp " ++ loopCond2 ++ "\n",
                        BStr $ loopStart2 ++ ":\n",
                        BStr $ "\tadd $1, " ++ showRegLoc argRegLoc0 ++ "\n",
                        BStr   "\tadd $1, %rax\n",
                        BStr $ loopCond2 ++ ":\n",
                        BStr   "\tmovb 0(%rax), %dl\n",
                        BStr   "\ttest %dl, %dl\n",
                        BStr $ "\tjnz " ++ loopStart2 ++ "\n",
                        
                        BStr   "\tcall malloc\n",
                        moveRegsLocs (Reg rax) argRegLoc0,
                           
                        BStr $ "\tjmp " ++ loopCond3 ++ "\n",
                        BStr $ loopStart3 ++ ":\n",
                        BStr $ "\tmovb %dl, 0(" ++ showRegLoc argRegLoc0 ++ ")\n",
                        BStr $ "\tadd $1, " ++ showRegLoc argRegLoc0 ++ "\n",
                        BStr   "\tadd $1, %r12\n",
                        BStr $ loopCond3 ++ ":\n",
                        BStr   "\tmovb 0(%r12), %dl\n",
                        BStr   "\ttest %dl, %dl\n",
                        BStr $ "\tjnz " ++ loopStart3 ++ "\n",
                        
                        BStr $ "\tjmp " ++ loopCond4 ++ "\n",
                        BStr $ loopStart4 ++ ":\n",
                        BStr $ "\tmovb %dl, 0(" ++ showRegLoc argRegLoc0 ++ ")\n",
                        BStr $ "\tadd $1, " ++ showRegLoc argRegLoc0 ++ "\n",
                        BStr   "\tadd $1, %r13\n",
                        BStr $ loopCond4 ++ ":\n",
                        BStr   "\tmovb 0(%r13), %dl\n",
                        BStr   "\ttest %dl, %dl\n",
                        BStr $ "\tjnz " ++ loopStart4 ++ "\n",
                        
                        BStr $ "\tmovb $0, 0(" ++ showRegLoc argRegLoc0 ++ ")\n",
                        BStr   "\tpop %r13\n",
                        BStr   "\tpop %r12\n",
                        BStr $ "\tpop " ++ showRegLoc argRegLoc0 ++ "\n",
                        moveRegsLocs (Reg rax) r
                    ]
        _ -> do
            (code1, r1) <- compileExpr expr0
            (code15, r15) <- maybeMoveReg r1
            (code2, r2) <- compileExpr expr1
            let isReg = case (r2, r15) of
                    (Reg _, _) -> True
                    (_, Reg _) -> True
                    _ -> False
            let tmpReg = if r == argRegLoc0
                then argRegLoc1
                else argRegLoc0
            let codeAdd = case (isReg, op) of
                    (True, Plus _) -> BLst [
                            moveRegsLocs r2 tmpReg,
                            moveRegsLocs r15 r,
                            BStr $ "\tadd " ++ showRegLoc tmpReg ++ ", " ++ showRegLoc r ++ "\n"
                        ]
                    (False, Plus _) -> BLst [
                            moveRegsLocs r2 tmpReg,
                            moveRegsLocs r15 r,
                            BStr $ "\tadd " ++ showRegLoc tmpReg ++ ", " ++ showRegLoc r ++ "\n"
                        ]
                    (True, Minus _) -> BLst [
                            moveRegsLocs r2 tmpReg,
                            moveRegsLocs r15 r,
                            BStr $ "\tsub " ++ showRegLoc tmpReg ++ ", " ++ showRegLoc r ++ "\n"
                        ]
                    (False, Minus _) -> BLst [
                            moveRegsLocs r2 tmpReg,
                            moveRegsLocs r15 r,
                            BStr $ "\tsub " ++ showRegLoc tmpReg ++ ", " ++ showRegLoc r ++ "\n"
                        ]
            return $ BLst [
                    code1,
                    code15,
                    code2,
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
            moveRegsLocs (Lit 1) r,
            BStr $ "\tjmp " ++ ln ++ "\n",
            BStr $ lf ++ ":\n",
             moveRegsLocs (Lit 0) r,
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
            moveRegsLocs (Lit 1) r,
            BStr $ "\tjmp " ++ ln ++ "\n",
            BStr $ lf ++ ":\n",
            moveRegsLocs (Lit 0) r,
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
            moveRegsLocs (Lit 1) r,
            BStr $ "\tjmp " ++ ln ++ "\n",
            BStr $ lf ++ ":\n",
            moveRegsLocs (Lit 0) r,
            BStr $ ln ++ ":\n"
        ]
compileExpr' expr r = do
    (code, rr) <- compileExpr expr
    return $ BLst [
            code,
            moveRegsLocs rr r
        ]

fillArgs :: [RegLoc] -> [Expr] -> CompilerMonad (StringBuilder, Int)
fillArgs ((Reg reg):regLocs) (expr:exprs) = do
    let argRegLoc = Reg reg
    freeCode <- freeRegLoc argRegLoc
    (exprCode, r) <- compileExpr expr
    (moveCode, regLoc) <- maybeMoveReg r
    (tailCode, stackAdd) <- fillArgs regLocs exprs
    return (BLst [
            freeCode,
            exprCode,
            moveCode,
            tailCode,
            moveRegsLocs regLoc argRegLoc
        ],
        stackAdd)
fillArgs regLocs (expr:exprs) = do
    (exprCode, reg) <- compileExpr expr
    (tailCode, stackAdd) <- fillArgs regLocs exprs
    return (BLst [
            exprCode,
            moveRegsLocs reg (Reg rax),
            BStr   "\tpush %rax\n",
            tailCode
        ],
        stackAdd + 8)
fillArgs _ [] = return (BLst [], 0)

compileExpr :: Expr -> CompilerMonad (StringBuilder, RegLoc)
-- compileExpr (ENew pos newVar) = 
compileExpr (EVar pos var) = do
    getVarRegLoc var
compileExpr (ELitInt pos n) = return (BLst [], Lit $ fromIntegral n)
compileExpr (ELitTrue pos) = compileExpr (ELitInt pos 1)
compileExpr (ELitFalse pos) = compileExpr (ELitInt pos 0)
compileExpr (ELitArr pos elems) = throwError "unimplemented"
compileExpr (ELitNull pos classIdent) = compileExpr (ELitInt pos 0)
compileExpr (EApp pos var exprs) = do
    (fillCode, stackAdd') <- fillArgs (argRegLocs argRegCount) exprs
    let (codeAlignStack, stackAdd) = if mod stackAdd' 16 > 0
        then (BStr $ "\tsub " ++ showRegLoc (Lit (16 - mod stackAdd' 16)) ++ ", " ++ showRegLoc (Reg rsp) ++ "\n", stackAdd' + 16 - mod stackAdd' 16)
        else (BLst [], stackAdd')
    let codeStackRestore = if stackAdd > 0
        then BStr $ "\tadd " ++ showRegLoc (Lit stackAdd) ++ ", " ++ showRegLoc (Reg rsp) ++ "\n"
        else BLst []
    return (
            BLst [
                fillCode,
                BStr $ "\tcall " ++ showVar var ++ "\n", -- TODO Maybe check for arrays
                codeStackRestore
            ],
            Reg rax
        )
-- compileExpr (EString pos str) = 
compileExpr (ENeg pos expr) = do
    (code, regLoc) <- compileExpr expr
    let regLoc2 = if regLoc == Reg rax
        then argRegLoc0
        else Reg rax
    case regLoc of
        Lit n -> return (BLst [], Lit (-n))
        _ -> return (BLst [
                    code,
                    moveRegsLocs (Lit 0) regLoc2,
                    BStr $ "\tsub " ++ showRegLoc regLoc ++ ", " ++ showRegLoc regLoc2 ++ "\n",
                    moveRegsLocs regLoc2 regLoc
                ], regLoc)
compileExpr (ENot pos expr) = do
    (code, r) <- compileExpr expr
    return (BLst [
            code,
            moveRegsLocs r (Reg rax),
            BStr $ "\txorq $1, " ++ showRegLoc (Reg rax) ++ "\n"
        ]
        , Reg rax)
compileExpr (EMul pos expr1 op expr2) = do
    (code1, r1) <- compileExpr expr1
    (code15, r15) <- maybeMoveReg r1
    (code2, r2) <- compileExpr expr2
    (code25, r25) <- case r2 of
        Lit _ -> do
            r25 <- getFreeRegLoc
            return (moveRegsLocs r2 r25, r25)
        _ -> maybeMoveReg r2
    let (codeMul, outReg) = case op of
            Times _ -> (BStr $ "\timulq " ++ showRegLoc r25 ++ "\n", rax)
            Div _ -> (BStr $ "\tidivq " ++ showRegLoc r25 ++ "\n", rax)
            Mod _ -> (BStr $ "\tidivq " ++ showRegLoc r25 ++ "\n", rdx)
    return (BLst [
            code1,
            code15,
            code2,
            code25,
            moveRegsLocs r15 (Reg rax),
            BStr   "\tcqto\n",
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

compileStmt :: Stmt -> CompilerMonad (StringBuilder, Env->Env)
compileStmt (Empty pos) = return (BLst [], id)
compileStmt (BStmt pos (Block _bPos [])) = compileStmt (Empty pos)
compileStmt (BStmt pos (Block bPos (stmt:stmts))) = do
    (code1, envMod) <- compileStmt stmt
    (code2, _) <- local envMod $ compileStmt (BStmt pos (Block bPos stmts))
    return (BLst [
            code1,
            code2
        ], id)
compileStmt (Decl pos tp []) = compileStmt (Empty pos)
compileStmt (Decl _pos tp (decl:decls)) = do
    let (ident, expr) = case decl of
            NoInit pos ident -> (ident, ELitInt pos 0)
            Init pos ident expr -> (ident, expr)
    loc <- newLoc
    regLoc <- getNextStack -- TODO add using registers
    ((lt, l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (
        (Data.Map.insert loc tp lt, l), 
        Data.Map.insert loc regLoc vrc,
        Data.Map.insert regLoc [IdentUse ident] rlu, 
        nextLabel, 
        stackState, 
        strCodes) -- TODO check if [ident] is correct
    codeHead <- compileExpr' expr regLoc
    let envMod1 = first (Data.Map.insert ident loc)
    (codeTail, envMod2) <- local envMod1 (compileStmt (Decl _pos tp decls))
    return (BLst [codeHead, codeTail], envMod1 . envMod2)
compileStmt (Ass pos var expr) = do
    (codeGetVar, regLoc) <- getVarRegLoc var
    codeExpr <- compileExpr' expr regLoc
    return (BLst [
            codeGetVar,
            codeExpr
        ], id)
compileStmt (Incr pos var) = do
    (codeGetVar, regLoc) <- getVarRegLoc var
    case regLoc of
        Reg reg -> return (BStr $ "\tadd $1, " ++ showReg reg ++ "\n", id)
        _ -> compileStmt (Ass pos var (EAdd pos (ELitInt pos 1) (Plus pos) (EVar pos var)))
compileStmt (Decr pos var) = do
    (codeGetVar, regLoc) <- getVarRegLoc var
    case regLoc of
        Reg reg -> return (BStr $ "\tsub $1, " ++ showReg reg ++ "\n", id)
        _ -> compileStmt (Ass pos var (EAdd pos (EVar pos var) (Minus pos) (ELitInt pos 1)))
compileStmt (Ret pos expr) = do
    code <- compileExpr' expr (Reg rax)
    return (BLst [
            code,
            BFil filRetN
        ], id)
compileStmt (VRet pos) = return (BFil filRetN, id)
compileStmt (Cond pos expr stmt) = do
    labelTrue <- newLabel
    labelExit <- newLabel
    codeCond <- compileIf expr labelTrue labelExit
    (codeTrue, trueEnvMod) <- compileStmt stmt
    return (BLst [
            codeCond,
            BStr $ labelTrue ++ ":\n",
            codeTrue,
            BStr $ labelExit ++ ":\n"
        ], id)
compileStmt (CondElse pos expr stmtTrue stmtFalse) = do
    labelTrue <- newLabel
    labelFalse <- newLabel
    labelExit <- newLabel
    codeCond <- compileIf expr labelTrue labelFalse
    (codeTrue, trueEnvMod) <- compileStmt stmtTrue
    (codeFalse, falseEnvMod) <- compileStmt stmtFalse
    return (BLst [
            codeCond,
            BStr $ labelTrue ++ ":\n",
            codeTrue,
            BStr $ "\tjmp " ++ labelExit ++ "\n",
            BStr $ labelFalse ++ ":\n",
            codeFalse,
            BStr $ labelExit ++ ":\n"
        ], id)
compileStmt (While pos expr stmt) = do
    labelLoop <- newLabel
    labelCond <- newLabel
    labelExit <- newLabel
    codeCond <- compileIf expr labelLoop labelExit
    (codeLoop, blockEnvMod) <- compileStmt stmt
    return (BLst [
            BStr $ "\tjmp " ++ labelCond ++ "\n",
            BStr $ labelLoop ++ ":\n",
            codeLoop,
            BStr $ labelCond ++ ":\n",
            codeCond,
            BStr $ labelExit ++ ":\n"
        ], id)
compileStmt (For pos incrTp incrIdent incrSet cond incrStmt blockStmt) = throwError "unimplemented"
compileStmt (ForEach pos elemTp elemIdent arrExpr blockStmt) = throwError "unimplemented"
compileStmt (SExp pos expr) = do
    (code, _r) <- compileExpr expr
    return (code, id)

addArgs' :: Stmt -> [RegLoc] -> [Arg] -> [(RegLoc, Arg)] -> CompilerMonad (StringBuilder, StringBuilder, Env -> Env)
addArgs' stmt _ [] [] = do
    (codeStmt, envMod) <- compileStmt stmt
    return (BLst [], codeStmt, envMod)
addArgs' stmt regLocs [] ((regLocIn, Arg pos tp ident):moveArgs) = do
    loc <- newLoc
    regLocOut <- getFreeRegLoc
    ((lt,l), vrc, rlu, nextLabel, (currStack, maxStack), strCodes) <- get
    (envVar, envClass) <- ask
    let codeMov = moveRegsLocs regLocIn regLocOut
    put (
        (Data.Map.insert loc tp lt, l), 
        Data.Map.insert loc regLocOut vrc, 
        Data.Map.insert regLocOut [IdentUse ident] rlu, 
        nextLabel, 
        (currStack, maxStack), 
        strCodes)
    (codeMoves, codeStmt, envModRet) <- local (first (Data.Map.insert ident loc)) (addArgs' stmt regLocs [] moveArgs)
    return (BLst [codeMoves, codeMov], codeStmt, envModRet)
addArgs' stmt (regLoc:regLocs) ((Arg pos tp ident):args) moveArgs = do
    loc <- newLoc
    ((lt,l), vrc, rlu, nextLabel, (currStack, maxStack), strCodes) <- get
    (envVar, envClass) <- ask
    put (
            (Data.Map.insert loc tp lt, l), 
            Data.Map.insert loc regLoc vrc, 
            Data.Map.insert regLoc [IdentUse ident] rlu, 
            nextLabel, 
            (currStack, maxStack), 
            strCodes)
    (codeMoves, codeStmt, envModRet) <- local (first (Data.Map.insert ident loc)) (addArgs' stmt regLocs args moveArgs)
    return (codeMoves, codeStmt, envModRet)
addArgs' stmt regLocs args moveArgs = throwError $ "addArgs' stmt regLocs:" ++ show regLocs ++ "args: " ++ show args ++ "moveArgs" ++ show moveArgs

moveRegArgs :: Int -> [RegLoc] -> [Arg] -> CompilerMonad ([RegLoc], [Arg], [(RegLoc, Arg)])
moveRegArgs 0 ((Reg r):regLocs) (arg:args) = do
    (shortenedArgRegLocs, shortenedArgs, moveArgs) <- moveRegArgs 0 regLocs args
    return (shortenedArgRegLocs, shortenedArgs, (Reg r, arg):moveArgs)
moveRegArgs 0 regLocs args = return (regLocs, args, [])
moveRegArgs n (regLoc:regLocs) (arg:args) = do
    (shortenedArgRegLocs, shortenedArgs, moveArgs) <- moveRegArgs (n-1) regLocs args
    return (shortenedArgRegLocs, shortenedArgs, (regLoc, arg):moveArgs)
moveRegArgs n regLocs [] = return (regLocs, [], [])

addArgs :: Int -> Stmt -> [Arg] -> CompilerMonad (StringBuilder, StringBuilder, Env -> Env)
addArgs maxAppArgs stmt args =
    if maxAppArgs == 0
        then addArgs' stmt (argRegLocs (length args)) args []
        else do 
            let regLocs = argRegLocs (length args)
            (shortenedArgRegLocs, shortenedArgs, moveArgs) <- moveRegArgs maxAppArgs regLocs args
            addArgs' stmt shortenedArgRegLocs shortenedArgs moveArgs

compileTopDefs :: StringBuilder -> [TopDef] -> CompilerMonad StringBuilder
compileTopDefs code ((FnDef pos tp ident args block):lst) = do
    (lt0, vrc0, rlu0, nextLabel0, stackStateOld0, strCodes0) <- get
    put (lt0, Data.Map.empty, Data.Map.empty, nextLabel0, (8, 8), strCodes0)
    let maxAppArgs = digStmtInfoPub (BStmt pos block)
    (codeMov, currCode, _) <- addArgs maxAppArgs (BStmt pos block) args
    (lt, vrc, rlu, nextLabel, (oldStack, oldStackMax), strCodes) <- get
    let stackMax = 32 * div (oldStackMax + 31) 32
    compileTopDefs (BLst [
            code,
            BStr $ showIdent ident ++ ":\n"
                ++ "\tpush %rbp\n"
                ++ "\tmovq %rsp, %rbp\n"
                ++ "\tsub $" ++ show stackMax ++ ", %rsp\n",
            codeMov,
            fillStringBuilder (Data.Map.singleton filRetN (
                   "\tmovq %rbp, %rsp\n"
                ++ "\tpop %rbp\n"
                ++ "\tret\n")) (BLst [currCode, BFil filRetN])
        ]) lst
compileTopDefs code ((ClassDef pos ident elems):lst) = throwError "unimplemented"
compileTopDefs code ((ClassExt pos classIdent parentIdent elems):lst) = throwError "unimplemented"
compileTopDefs code [] = do return code

compileBuiltInFunctions :: [BuiltInFunction] -> CompilerMonad (StringBuilder, StringBuilder)
compileBuiltInFunctions [] = return (BLst [], BLst [])
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

compileProgram' :: Program -> CompilerMonad String
compileProgram' (Program pos topDefs) = do
    (buildInCode, builtInData) <- compileBuiltInFunctions builtInFunctions
    code <- compileTopDefs (BLst []) topDefs
    (lt, vrl, rlu, l, stackDepth, strCodes) <- get
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

argsToTypes :: [Arg] -> [Type]
argsToTypes = Prelude.map argToType

addEverything :: [BuiltInFunction] -> [TopDef] -> Program -> CompilerMonad String
addEverything [] (topDef:topDefs) program = do
    case topDef of
        FnDef pos retTp ident args block -> do
            loc <- newLoc
            let tp = Fun pos retTp (argsToTypes args)
            insertLocTp loc tp
            local (first $ Data.Map.insert ident loc) (addEverything [] topDefs program)
        _ -> throwError "unimplemented"
addEverything ((ident,tp,_,_):bIFs) topDefs program = do
    loc <- newLoc
    insertLocTp loc tp
    local (first $ Data.Map.insert ident loc) (addEverything bIFs topDefs program)
addEverything [] [] program = compileProgram' program

compileProgram :: Program -> CompilerMonad String
compileProgram (Program pos topDefs) = addEverything builtInFunctions topDefs (Program pos topDefs)