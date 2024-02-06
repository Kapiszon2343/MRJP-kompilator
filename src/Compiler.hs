{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use foldr" #-}
{-# HLINT ignore "Use guards" #-}
module Compiler where

import Data.Map
import Data.Maybe (fromMaybe)
import Data.Bifunctor ( first, Bifunctor (bimap) )
import Control.Monad.State
import Control.Monad.Reader ( ReaderT (runReaderT), MonadReader(local, ask), asks )
import Control.Monad.Except

import Latte.Abs
import Common
import qualified Text.ParserCombinators.ReadP as Data.Map
import GHC.IO.Handle.Internals (readTextDevice)
import InfoDigger (digStmtInfoPub)
import Control.Exception.Base (throw)
import Distribution.Compat.CharParsing (between)

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

argRegLocs :: Int -> [RegLoc]
argRegLocs = argRegLocs' argRegs

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
                Just ((attrMap, _, _),_) -> do
                    let attr = Data.Map.lookup ident attrMap
                    case attr of
                        Just (tp, _) -> return tp
                        Nothing -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ " does not have attribute " ++ showIdent ident
                Nothing -> throwError $ "Something went horribly wrong!!\n Could not find class " ++ showIdent classIdent ++ "of variable " ++ showVar var ++ " at: " ++ showPos pos
        _ -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ "does not have attributes"

getClassForm :: Ident -> CompilerMonad ClassForm
getClassForm classIdent = do
    (_, envClass)<- ask
    case Data.Map.lookup classIdent envClass of
        Nothing -> throwError $ "unregistered class " ++ showIdent classIdent
        Just (form, parentIdent) -> return form

getAttrMap :: Ident -> CompilerMonad ClassAttrs
getAttrMap classIdent = do
    (attrMap, _, _) <- getClassForm classIdent
    return attrMap

newLabel :: CompilerMonad String
newLabel = do
    (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (lt, vrc, rlu, nextLabel+1, stackState, strCodes)
    return $ "label_" ++ show nextLabel

functionLabel :: Var -> CompilerMonad String
functionLabel (IdentVar _ ident) = return $ "fun_" ++ showIdent ident
functionLabel (ArrayVar _ var _) = throwError "functional variable is not unimplemented"
functionLabel (AttrVar pos var ident) = do
    classType <- getVarType var
    case classType of
        Class _ classIdent -> functionLabel' classIdent ident
        _ -> throwError $ showVar var ++ " is not a class at: " ++ showPos pos

functionLabel' classIdent functionIdent = return $ "classFun_" ++ showIdent classIdent ++ "_" ++ showIdent functionIdent

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
        then throwError "Attempting to get not existing register. No code should be able to reach this message"
        else do
            (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
            case lookupArr (Reg r) rlu of
                [] -> return r
                _ -> getFreeReg' (r+1)

getFreeRegLoc' :: [Reg] -> CompilerMonad RegLoc
getFreeRegLoc' [] = getNextStack
getFreeRegLoc' (reg:regs) = do
    (lt, vrc, rlu, nextLabel,  (currStackSize, maxStackSize), strCodes) <- get
    case lookupArr (Reg reg) rlu of
        [] -> do
            put (lt, vrc, Data.Map.insert (Reg reg) [TMPUse] rlu, nextLabel, (currStackSize, maxStackSize), strCodes)
            return $ Reg reg
        _ -> getFreeRegLoc' regs

getFreeRegLoc :: CompilerMonad RegLoc
getFreeRegLoc = getFreeRegLoc' stableRegs

makeIntoReg :: RegLoc -> Reg -> CompilerMonad (StringBuilder, RegLoc)
makeIntoReg (Reg r) _ = return (BLst [], Reg r)
makeIntoReg regLoc r = return (moveRegsLocs regLoc (Reg r), Reg r)

makeIntoReg2 :: RegLoc -> RegLoc -> Reg -> Reg -> CompilerMonad (StringBuilder, RegLoc, RegLoc)
makeIntoReg2 (Reg r1) (Reg r2) _ _ = return (BLst [], Reg r1, Reg r2)
makeIntoReg2 (Reg r) regLoc r1 r2 = if r2 == r
    then return (moveRegsLocs regLoc (Reg r1), Reg r, Reg r1)
    else return (moveRegsLocs regLoc (Reg r2), Reg r, Reg r2)
makeIntoReg2 regLoc (Reg r) r1 r2 = do
    (code, regLoc2, regLoc1) <- makeIntoReg2 (Reg r) regLoc r2 r1
    return (code, regLoc1, regLoc2)
makeIntoReg2 regLoc1 regLoc2 r1 r2 = return (BLst [
        moveRegsLocs regLoc1 (Reg r1),
        moveRegsLocs regLoc2 (Reg r2)
    ], Reg r1, Reg r2)

makeIntoLocal2 :: RegLoc -> RegLoc -> Reg -> Reg -> CompilerMonad (StringBuilder, RegLoc, RegLoc)
makeIntoLocal2 (Reg r1) (Reg r2) _ _ = return (BLst [], Reg r1, Reg r2)
makeIntoLocal2 (Reg r1) (Lit n2) _ _ = return (BLst [], Reg r1, Lit n2)
makeIntoLocal2 (Lit n1) (Lit n2) _ _ = return (BLst [], Lit n1, Lit n2)
makeIntoLocal2 regLoc (Reg r) r1 r2 = do
    (code, regLoc2, regLoc1) <- makeIntoLocal2 (Reg r) regLoc r2 r1
    return (code, regLoc1, regLoc2)
makeIntoLocal2 regLoc (Lit n) r1 r2 = do
    (code, regLoc2, regLoc1) <- makeIntoLocal2 (Lit n) regLoc r2 r1
    return (code, regLoc1, regLoc2)
makeIntoLocal2 (Reg r) regLoc r1 r2 = if r2 == r
    then return (moveRegsLocs regLoc (Reg r1), Reg r, Reg r1)
    else return (moveRegsLocs regLoc (Reg r2), Reg r, Reg r2)
makeIntoLocal2 (Lit n) regLoc r1 r2 = return (moveRegsLocs regLoc (Reg r2), Lit n, Reg r2)
makeIntoLocal2 regLoc1 regLoc2 r1 r2 = return (BLst [
        moveRegsLocs regLoc1 (Reg r1),
        moveRegsLocs regLoc2 (Reg r2)
    ], Reg r1, Reg r2)

removeFirstTmp :: [LocUse] -> [LocUse]
removeFirstTmp [] = []
removeFirstTmp (TMPUse:refs) = refs
removeFirstTmp (ref:refs) = ref:removeFirstTmp refs

reserveRegLoc :: RegLoc -> Loc -> Type -> [LocUse] -> CompilerMonad ()
reserveRegLoc regLoc loc tp [IdentUse ident] = do
    ((lt, l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (
        (Data.Map.insert loc tp lt, l), 
        Data.Map.insert loc regLoc vrc,
        Data.Map.insert regLoc [IdentUse ident] rlu, 
        nextLabel, 
        stackState, 
        strCodes) -- TODO check if [ident] is correct

releaseTmpRegLoc :: RegLoc -> CompilerMonad ()
releaseTmpRegLoc regLoc = do
    (lt, vrc, rlu, nextLabel, stackState, strCodes) <- get
    let ref = lookupArr regLoc rlu
    let newRef = removeFirstTmp ref
    put (lt, vrc, Data.Map.insert regLoc newRef rlu, nextLabel, stackState, strCodes)

releaseTmpRegLocs :: [RegLoc] -> CompilerMonad ()
releaseTmpRegLocs [] = return ()
releaseTmpRegLocs (regLoc:regLocs) = do
    releaseTmpRegLoc regLoc
    releaseTmpRegLocs regLocs

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
        Nothing -> throwError ("undefined variable " ++ showIdent ident ++ " at " ++ show pos)
        Just regLoc -> return regLoc

fixMemRegLoc :: RegLoc -> CompilerMonad (StringBuilder, RegLoc, [RegLoc], StringBuilder)
fixMemRegLoc (Mem dist regLocStart regLocStep step) = if isRegLocLocal regLocStart && isRegLocLocal regLocStep
    then return (BLst [], Mem dist regLocStart regLocStep step, [], BLst [])
    else if isRegLocLocal regLocStep
        then do
            (fixCode, regLocStart2, regLocsToRelease, releaseCode) <- fixMemRegLoc regLocStart
            rVar0 <- getFreeRegLoc
            let (codeGetVarSpace, codeReleaseVarSpace, rVar) = if isRegLocLocal rVar0
                then (BLst [], BLst [], rVar0)
                else if regLocStep == Reg 12
                    then (moveRegsLocs (Reg 13) rVar0, moveRegsLocs rVar0 (Reg 13), Reg 13)
                    else (moveRegsLocs (Reg 12) rVar0, moveRegsLocs rVar0 (Reg 12), Reg 12)
            releaseTmpRegLocs regLocsToRelease
            return (BLst [
                fixCode,
                codeGetVarSpace,
                moveRegsLocs regLocStart2 rVar,
                releaseCode
                ], Mem dist rVar regLocStep step, [regLocStart2, rVar0], codeReleaseVarSpace)
        else do 
            (fixCode0, regLocStart, regLocsToRelease0, releaseCode0) <- fixMemRegLoc regLocStart
            (fixCode1, regLocStep, regLocsToRelease1, releaseCode1) <- fixMemRegLoc regLocStep
            rVar0 <- getFreeRegLoc
            (codeGetVarSpace, codeReleaseVarSpace, rVar) <- if isRegLocLocal rVar0
                then return (BLst [], BLst [], rVar0)
                else do
                    return (moveRegsLocs (Reg 12) rVar0, moveRegsLocs rVar0 (Reg 12), Reg 12)
            rIdx0 <- getFreeRegLoc
            (codeGetIdxSpace, codeReleaseIdxSpace, rIdx) <- if isRegLocLocal rIdx0
                then return (BLst [], BLst [], rIdx0)
                else do
                    return (moveRegsLocs (Reg 13) rIdx0, moveRegsLocs rIdx0 (Reg 13), Reg 13)
            let codeGetSpace = BLst [codeGetVarSpace, codeGetIdxSpace]
            let codeReleaseSpace = BLst [codeReleaseVarSpace, codeReleaseIdxSpace]
            releaseTmpRegLocs regLocsToRelease0
            releaseTmpRegLocs regLocsToRelease1
            return (BLst [
                fixCode0,
                fixCode1,
                codeGetSpace,
                moveRegsLocs regLocStart rVar,
                moveRegsLocs regLocStep rIdx,
                releaseCode0,
                releaseCode1
                ], Mem dist rVar rIdx step, [rVar0, rIdx0], codeReleaseSpace)
fixMemRegLoc regLoc = return (BLst [], regLoc, [], BLst [])

extractMemRegLoc :: RegLoc -> CompilerMonad (StringBuilder, RegLoc)
extractMemRegLoc (Mem dist regLocStart regLocStep step) = if isRegLocLocal regLocStart && isRegLocLocal regLocStep
    then return (BLst [], Mem dist regLocStart regLocStep step)
    else do
        (extractCode0, regLocStartNew) <- extractMemRegLoc regLocStart
        (extractCode1, regLocStepNew) <- extractMemRegLoc regLocStep
        (codeMake, rVar, rIdx) <- makeIntoLocal2 regLocStartNew regLocStepNew rax rdx
        releaseTmpRegLoc regLocStartNew
        releaseTmpRegLoc regLocStart
        releaseTmpRegLoc regLocStepNew
        releaseTmpRegLoc regLocStep
        retRegLoc <- getFreeRegLoc
        return (BLst [
            extractCode0,
            extractCode1,
            codeMake,
            moveRegsLocs (Mem dist rVar rIdx step) retRegLoc
            ], retRegLoc)
extractMemRegLoc regLoc = return (BLst [], regLoc)

getVarRegLoc :: Var -> CompilerMonad (StringBuilder, RegLoc)
getVarRegLoc (IdentVar pos ident) = do
    regLoc <- getIdentRegLoc pos ident
    return (BLst [], regLoc)
getVarRegLoc (ArrayVar pos arrVar expr) = do
    (codeVar, regVar) <- getVarRegLoc arrVar
    (codeIdx, regIdx) <- compileExpr expr
    return (BLst [codeVar, codeIdx], Mem 16 regVar regIdx 8)
getVarRegLoc (AttrVar pos var attrIdent) = do
    tp <- getVarType var
    (codeVar, regVar) <- getVarRegLoc var
    case tp of
        Array _pos _baseTp -> do
            return (BLst [codeVar], Mem 8 regVar (Lit 0) 0)
        Class _pos classIdent -> do
            attrMap <- getAttrMap classIdent
            (tp, attrLoc) <- case Data.Map.lookup attrIdent attrMap of
                    Just (tp, attrDepth) -> return (tp, attrDepth)
                    Nothing -> throwError $ "Attribute " ++ showIdent attrIdent ++ " doesn't exist in class " ++ show tp ++ "at: " ++ showPos pos ++ "\n"
            case attrLoc of
                AttrLocVar attrDepth -> return (BLst [codeVar], Mem attrDepth regVar (Lit 0) 0)
                AttrLocMet _ -> throwError "unimplemented"
        _ -> throwError $ "Attribute call on type " ++ show tp ++ "at: " ++ showPos pos ++ "\n"

maybeMoveReg' :: [Reg] -> RegLoc -> CompilerMonad (StringBuilder, RegLoc)
maybeMoveReg' [] reg = return (BLst [], reg)
maybeMoveReg' (reg:regs) regLoc = if regLoc == Reg reg
    then do
        newRegLoc <- getFreeRegLoc
        return (moveRegsLocs regLoc newRegLoc, newRegLoc)
    else maybeMoveReg' regs regLoc

maybeMoveReg :: RegLoc -> CompilerMonad (StringBuilder, RegLoc)
maybeMoveReg = maybeMoveReg' (rax:tmpRegs)

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
    (getCode, regLoc2) <- getVarRegLoc var
    (fixCode, regLoc) <- extractMemRegLoc regLoc2
    return $ BLst [
        getCode,
        fixCode,
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
    releaseTmpRegLoc r1
    releaseTmpRegLoc r2
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
    releaseTmpRegLoc regLoc
    return $ BLst [
        code,
        moveRegsLocs regLoc (Reg rax),
        BStr  "\ttest %rax, %rax\n",
        BStr $ "\tjz " ++ lf ++ "\n",
        BStr $ "\tjmp " ++ lt ++ "\n"
        ]

compileExprs' :: [Expr] -> [RegLoc] -> StringBuilder -> CompilerMonad StringBuilder
compileExprs' [] _ _ = return $ BLst []
compileExprs' [expr] [regLoc] _ = compileExpr' expr regLoc
compileExprs' (expr:exprs) (regLoc:regLocs) betweenCode = do
    codeHead <- compileExpr' expr regLoc
    codeTail <- compileExprs' exprs regLocs betweenCode
    return $ BLst [codeHead, betweenCode, codeTail]

compileExpr' :: Expr -> RegLoc -> CompilerMonad StringBuilder
compileExpr' (ENew pos newVar) r = do
    case newVar of
        NewBase newPos tp -> case tp of
            Class tpPos classIdent -> do
                (envVar, envClass) <- ask
                (classForm, parentName) <- case Data.Map.lookup classIdent envClass of
                    Nothing -> throwError $ "Could not find class named " ++ showIdent classIdent ++ " at: " ++ showPos tpPos
                    Just (classForm, classSize) -> return (classForm, classSize)
                let (attrs, _, (classSize, methodSize)) = classForm
                let reg = case r of
                        Reg _ -> r
                        _ -> argRegLoc2
                loopLabel <- newLabel
                let classAttrCount = div (classSize - 16) 8
                let loopCode = if classAttrCount > 0 
                        then BLst [
                            BStr $ loopLabel ++ ":\n",
                            BStr $ "\tdecq " ++ showRegLoc argRegLoc1 ++ "\n",
                            moveRegsLocs (Lit 0) (Mem 16 reg argRegLoc1 8),
                            BStr $ "\ttest " ++ showRegLoc argRegLoc1 ++ ", " ++ showRegLoc argRegLoc1 ++ "\n",
                            BStr $ "\tjnz " ++ loopLabel ++ "\n"
                        ]
                        else BLst []
                return $ BLst [
                        moveRegsLocs (Lit classSize) argRegLoc0,
                        BStr   "\tcall malloc\n",
                        moveRegsLocs (Reg rax) reg,
                        BStr $ "\tleaq " ++ classLabel classIdent ++ "(%rip), " ++ showRegLoc argRegLoc1 ++ "\n", 
                        moveRegsLocs argRegLoc1 (Mem 8 reg (Lit 0) 0),
                        moveRegsLocs (Lit $ div (classSize - 16) 8) argRegLoc1,
                        loopCode,
                        moveRegsLocs reg r
                    ]
            Str tpPos -> return $ BLst [
                    moveRegsLocs (Lit 1) argRegLoc0,
                    BStr   "\tcall malloc\n",
                    moveRegsLocs (Lit 0) (Mem 0 (Reg rax) (Lit 0) 0),
                    moveRegsLocs (Reg rax) r
                ]
            _ -> compileExpr' (ELitInt pos 0) r
        NewArray newPos internalNew expr -> do
            regLocLen <- getFreeRegLoc
            let reg = case r of
                    Reg _ -> r
                    _ -> argRegLoc2
            exprCode <- compileExpr' expr argRegLoc0
            loopLabel <- newLabel
            loopSkipLabel <- newLabel
            releaseTmpRegLoc regLocLen
            return $ BLst [
                    exprCode,
                    moveRegsLocs argRegLoc0 regLocLen,
                    BStr $ "\tadd $2, " ++ showRegLoc argRegLoc0 ++ "\n",
                    BStr $ "\tshl $3, " ++ showRegLoc argRegLoc0 ++ "\n",
                    BStr   "\tcall malloc\n",
                    moveRegsLocs regLocLen argRegLoc1,
                    moveRegsLocs (Reg rax) reg,
                    moveRegsLocs argRegLoc1 (Mem 8 reg (Lit 0) 0),
                    BStr $ "\ttest " ++ showRegLoc argRegLoc1 ++ ", " ++ showRegLoc argRegLoc1 ++ "\n",
                    BStr $ "\tjz " ++ loopSkipLabel ++ "\n",
                    BStr $ loopLabel ++ ":\n",
                    BStr $ "\tdecq " ++ showRegLoc argRegLoc1 ++ "\n",
                    moveRegsLocs (Lit 0) (Mem 16 reg argRegLoc1 8),
                    BStr $ "\ttest " ++ showRegLoc argRegLoc1 ++ ", " ++ showRegLoc argRegLoc1 ++ "\n",
                    BStr $ "\tjnz " ++ loopLabel ++ "\n",
                    BStr $ loopSkipLabel ++ ":\n",
                    moveRegsLocs reg r
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
            if r /= r15
                then do
                    releaseTmpRegLoc r15
                    releaseTmpRegLoc r2
                else releaseTmpRegLoc r2
            let (tmpReg1, tmpReg2) = if r15 == Reg rax || r2 == Reg rdx
                then (Reg rdx, Reg rax)
                else (Reg rax, Reg rdx)
            stackSpace1 <- getNextStack
            stackSpace2 <- getNextStack
            return $ BLst [
                        code1,
                        code15,
                        code2,
                        moveRegsLocs r2 tmpReg2,
                        moveRegsLocs r15 tmpReg1,
                        moveRegsLocs (Reg 12) stackSpace1,
                        moveRegsLocs (Reg 13) stackSpace2,

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
                        moveRegsLocs stackSpace2 (Reg 13),
                        moveRegsLocs stackSpace1 (Reg 12),
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
            releaseTmpRegLoc r15
            releaseTmpRegLoc r2
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
    releaseTmpRegLoc rr
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
    releaseTmpRegLoc r
    releaseTmpRegLoc regLoc
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
    releaseTmpRegLoc reg
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
    (getCode, regLoc2) <- getVarRegLoc var
    (fixCode, regLoc) <- extractMemRegLoc regLoc2
    return (BLst [getCode, fixCode], regLoc)
compileExpr (ELitInt pos n) = return (BLst [], Lit $ fromIntegral n)
compileExpr (ELitTrue pos) = compileExpr (ELitInt pos 1)
compileExpr (ELitFalse pos) = compileExpr (ELitInt pos 0)
compileExpr (ELitArr pos elems) = throwError "unimplemented"
compileExpr (ELitNull pos classIdent) = compileExpr (ELitInt pos 0)
compileExpr (EApp pos var exprs) =
    case var of
        IdentVar posVar ident -> do
            (fillCode, stackAdd') <- fillArgs (argRegLocs argRegCount) exprs
            let (codeAlignStack, stackAdd) = if mod stackAdd' 16 > 0
                then (BStr $ "\tsub " ++ showRegLoc (Lit (16 - mod stackAdd' 16)) ++ ", " ++ showRegLoc (Reg rsp) ++ "\n", stackAdd' + 16 - mod stackAdd' 16)
                else (BLst [], stackAdd')
            let codeStackRestore = if stackAdd > 0
                then BStr $ "\tadd " ++ showRegLoc (Lit stackAdd) ++ ", " ++ showRegLoc (Reg rsp) ++ "\n"
                else BLst []
            labelF <- functionLabel var
            return (
                    BLst [
                        codeAlignStack,
                        fillCode,
                        BStr $ "\tcall " ++ labelF ++ "\n", -- TODO Maybe check for arrays
                        codeStackRestore
                    ],
                    Reg rax
                )
        AttrVar attrPos classVar funIdent -> do
            (getCode, regLoc2) <- getVarRegLoc classVar
            (fixCode, classRegLoc) <- extractMemRegLoc regLoc2
            r12Mem <- if classRegLoc == globalSelfRegLoc
                then return globalSelfRegLoc
                else getNextStack
            classTp <- getVarType classVar
            (envVar, envClass) <- ask
            classIdent <- case classTp of
                Class _ classIdent -> return classIdent
                _ -> throwError $ "unregistered class at: " ++ showPos pos
            attrMap <- getAttrMap classIdent
            attrLoc <- case Data.Map.lookup funIdent attrMap of
                Nothing -> throwError $ "No attribute " ++ showIdent funIdent ++ " in class " ++ showIdent classIdent ++ " at: "++ showPos pos
                Just (tp, attrLoc) -> return attrLoc
            methodDepth <- case attrLoc of
                AttrLocMet methodDepth -> return methodDepth
                _ -> throwError   "functional variable is no implemented in compiler"
            (fillCode, stackAdd') <- fillArgs (argRegLocs argRegCount) exprs
            let (codeAlignStack, stackAdd) = if mod stackAdd' 16 > 0
                then (BStr $ "\tsub " ++ showRegLoc (Lit (16 - mod stackAdd' 16)) ++ ", " ++ showRegLoc (Reg rsp) ++ "\n", stackAdd' + 16 - mod stackAdd' 16)
                else (BLst [], stackAdd')
            let codeStackRestore = if stackAdd > 0
                then BStr $ "\tadd " ++ showRegLoc (Lit stackAdd) ++ ", " ++ showRegLoc (Reg rsp) ++ "\n"
                else BLst []
            releaseTmpRegLocs [classRegLoc, r12Mem]
            labelF <- functionLabel var
            return (BLst [
                    getCode,
                    fixCode,
                    codeAlignStack,
                    fillCode,
                    moveRegsLocs globalSelfRegLoc r12Mem,
                    moveRegsLocs classRegLoc globalSelfRegLoc,
                    moveRegsLocs (Mem 8 globalSelfRegLoc (Lit 0) 0) (Reg rax),
                    moveRegsLocs (Mem methodDepth (Reg rax) (Lit 0) 0) (Reg rax),
                    --BStr $ "\tadd " ++ showRegLoc (Lit methodDepth) ++ ", " ++ showRegLoc (Reg rax) ++ "\n",
                    BStr $ "\tcall *" ++ showRegLoc (Reg rax)++ "\n",
                    -- BStr $ "\tcall " ++ labelF ++ "\n",
                    moveRegsLocs r12Mem globalSelfRegLoc,
                    codeStackRestore
                ], Reg rax)
        _ -> throwError "calling function from array is unimplemented"
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
    releaseTmpRegLoc r
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
    releaseTmpRegLoc r1
    releaseTmpRegLoc r15
    releaseTmpRegLoc r2
    releaseTmpRegLoc r25
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
    regLoc <- getNextStack
    reserveRegLoc regLoc loc tp [IdentUse ident]
    codeHead <- compileExpr' expr regLoc
    let envMod1 = first (Data.Map.insert ident loc)
    (codeTail, envMod2) <- local envMod1 (compileStmt (Decl _pos tp decls))
    return (BLst [codeHead, codeTail], envMod1 . envMod2)
compileStmt (Ass pos var expr) = do
    (codeGetVar, regLocVar0) <- getVarRegLoc var
    (codeFixVar, regLocVar, regLocsToRelease, codeFixVarReleases) <- fixMemRegLoc regLocVar0
    codeExpr <- compileExpr' expr regLocVar
    releaseTmpRegLocs regLocsToRelease
    return (BLst [
            codeGetVar,
            codeFixVar,
            codeExpr,
            codeFixVarReleases
        ], id)
compileStmt (Incr pos var) = do
    (codeGetVar, regLoc) <- getVarRegLoc var
    releaseTmpRegLoc regLoc
    case regLoc of
        Reg reg -> return (BStr $ "\tadd $1, " ++ showReg reg ++ "\n", id)
        _ -> compileStmt (Ass pos var (EAdd pos (ELitInt pos 1) (Plus pos) (EVar pos var)))
compileStmt (Decr pos var) = do
    (codeGetVar, regLoc) <- getVarRegLoc var
    releaseTmpRegLoc regLoc
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
compileStmt (For pos incrTp incrIdent incrSet cond incrStmt blockStmt) = do
    loc <- newLoc
    regLoc <- getFreeRegLoc
    ((lt, l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (
        (Data.Map.insert loc incrTp lt, l), 
        Data.Map.insert loc regLoc vrc,
        Data.Map.insert regLoc [IdentUse incrIdent] rlu, 
        nextLabel, 
        stackState, 
        strCodes)
    codeIncrSet <- compileExpr' incrSet regLoc
    let envMod1 = first (Data.Map.insert incrIdent loc)
    (retCode, _) <- local envMod1 $ compileStmt (
            While pos cond (BStmt pos (Block pos [
                blockStmt,
                incrStmt
            ])))
    ((lt, l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (
        (lt, l), 
        vrc,
        Data.Map.insert regLoc [] rlu, 
        nextLabel, 
        stackState, 
        strCodes)
    return (BLst [
            codeIncrSet,
            retCode
        ], id)
compileStmt (ForEach pos elemTp elemIdent arrExpr blockStmt) = do
    loc <- newLoc
    regLocArr <- getNextStack
    getArrCode <- compileExpr' arrExpr regLocArr
    regLocIt <- getNextStack
    let regLocElem = Mem 16 regLocArr regLocIt 8 
    ((lt, l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (
        (Data.Map.insert loc elemTp lt, l), 
        Data.Map.insert loc regLocElem vrc,
        Data.Map.insert regLocIt [IdentUse elemIdent] $ Data.Map.insert regLocArr [IdentUse elemIdent] rlu, 
        nextLabel, 
        stackState, 
        strCodes)
    let codeIncrSet = BLst [
            getArrCode,
            moveRegsLocs (Lit 0) regLocIt
            ]
    let envMod1 = first (Data.Map.insert elemIdent loc)
    labelLoop <- newLabel
    labelCond <- newLabel
    labelExit <- newLabel
    let (codeCond1, regLocArr2) = case regLocArr of
            Reg _ -> (BLst [], regLocArr)
            Lit _ -> (BLst [], regLocArr)
            _ -> (moveRegsLocs regLocArr argRegLoc1, argRegLoc1)
    let codeCond2 = case regLocIt of
            Reg _ -> BLst [
                    BStr $ "\tcmp " ++ showRegLoc (Mem 8 regLocArr2 (Lit 0) 0) ++ ", " ++ showRegLoc regLocIt ++ "\n",
                    BStr $ "\tjl " ++ labelLoop ++ "\n"
                ]
            _ -> BLst [
                    moveRegsLocs regLocIt (Reg rax),
                    BStr $ "\tcmp " ++ showRegLoc (Mem 8 regLocArr2 (Lit 0) 0) ++ ", " ++ showRegLoc (Reg rax) ++ "\n",
                    BStr $ "\tjl " ++ labelLoop ++ "\n"
                ]
    let codeCond = BLst [codeCond1, codeCond2]
    let codeIterate = BLst [
                BStr $ "\tincq " ++ showRegLoc regLocIt ++ "\n"
            ]
    let envMod = envMod1
    (codeLoop, blockEnvMod) <- local envMod $ compileStmt blockStmt
    let codeWhile = BLst [
                BStr $ "\tjmp " ++ labelCond ++ "\n",
                BStr $ labelLoop ++ ":\n",
                codeLoop,
                codeIterate,
                BStr $ labelCond ++ ":\n",
                codeCond,
                BStr $ labelExit ++ ":\n"
            ]
    ((lt, l), vrc, rlu, nextLabel, stackState, strCodes) <- get
    put (
        (lt, l), 
        vrc,
        Data.Map.insert regLocIt [] $ Data.Map.insert regLocArr [] rlu, 
        nextLabel, 
        stackState, 
        strCodes)
    return (BLst [
            codeIncrSet,
            codeWhile
        ], id)
compileStmt (SExp pos expr) = do
    (code, r) <- compileExpr expr
    releaseTmpRegLoc r
    return (code, id)

addArgs' :: Stmt -> [RegLoc] -> [Arg] -> [(RegLoc, Arg)] -> CompilerMonad (StringBuilder, StringBuilder, Env -> Env)
addArgs' stmt _ [] [] = do
    (codeStmt, envMod) <- compileStmt stmt
    return (BLst [], codeStmt, envMod)
addArgs' stmt regLocs [] ((regLocIn, Arg pos tp ident):moveArgs) = do
    loc <- newLoc
    regLocOut <- getNextStack
    reserveRegLoc regLocOut loc tp [IdentUse ident]
    let codeMov = moveRegsLocs regLocIn regLocOut
    (codeMoves, codeStmt, envModRet) <- local (first (Data.Map.insert ident loc)) (addArgs' stmt regLocs [] moveArgs)
    return (BLst [codeMoves, codeMov], codeStmt, envModRet)
addArgs' stmt (regLoc:regLocs) ((Arg pos tp ident):args) moveArgs = do
    loc <- newLoc
    reserveRegLoc regLoc loc tp [IdentUse ident]
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
        then -- addArgs' stmt (argRegLocs (length args)) args []
        do 
            let regLocs = argRegLocs (length args)
            (shortenedArgRegLocs, shortenedArgs, moveArgs) <- moveRegArgs maxAppArgs regLocs args
            addArgs' stmt shortenedArgRegLocs shortenedArgs moveArgs
        else do 
            let regLocs = argRegLocs (length args)
            (shortenedArgRegLocs, shortenedArgs, moveArgs) <- moveRegArgs maxAppArgs regLocs args
            addArgs' stmt shortenedArgRegLocs shortenedArgs moveArgs

stableRegsToStack' :: [Reg] -> CompilerMonad (StringBuilder, StringBuilder)
stableRegsToStack' [] = return (BLst [], BLst [])
stableRegsToStack' (reg:regs) = do
    (lt, vrc, rlu, nextLabel,  (currStackSize, maxStackSize), strCodes) <- get
    case Data.Map.lookup (Reg reg) rlu of
        Just _ -> do
            let regLoc = RBP (maxStackSize+8)
            put (lt, vrc, rlu, nextLabel,  (currStackSize, max maxStackSize (maxStackSize+8)), strCodes)
            (codePushTail, codePopTail) <- stableRegsToStack' regs
            let codePushThis = moveRegsLocs (Reg reg) regLoc
            let codePopThis = moveRegsLocs regLoc (Reg reg)
            return (BLst[codePushTail, codePushThis], BLst[codePopThis, codePopTail])
        Nothing -> stableRegsToStack' regs


stableRegsToStack :: CompilerMonad (StringBuilder, StringBuilder)
stableRegsToStack = stableRegsToStack' stableRegs

stableClassRegsToStack :: CompilerMonad (StringBuilder, StringBuilder)
stableClassRegsToStack = stableRegsToStack' $ tail stableRegs

compileClassElems' :: Ident -> [ClassElem] -> CompilerMonad (StringBuilder)
compileClassElems' _ [] = return (BLst [])
compileClassElems' selfIdent ((Attribute pos tp ident):classElems) = compileClassElems' selfIdent classElems
compileClassElems' selfIdent ((Method pos tp ident args block):classElems) = do
    (lt0, vrc0, rlu0, nextLabel0, stackStateOld0, strCodes0) <- get
    let maxAppArgs = digStmtInfoPub (BStmt pos block)
    (codeMov, currCode, _) <- addArgs maxAppArgs (BStmt pos block) args
    (codePush, codePop) <- stableClassRegsToStack
    (lt, vrc, rlu, nextLabel, (oldStack, oldStackMax), strCodes) <- get
    let stackMax = 16 * div (oldStackMax + 31) 16
    put (lt, vrc0, rlu0, nextLabel, stackStateOld0, strCodes)
    codeTail <- compileClassElems' selfIdent classElems
    labelF <- functionLabel' selfIdent ident
    return (
        BLst [
            BStr $ labelF ++ ":\n"
                ++ "\tpush %rbp\n"
                ++ "\tmovq %rsp, %rbp\n"
                ++ "\tsub $" ++ show stackMax ++ ", %rsp\n",
            codePush,
            codeMov,
            fillStringBuilder (Data.Map.singleton filRetN (
                    buildString codePop
                ++ "\tmovq %rbp, %rsp\n"
                ++ "\tpop %rbp\n"
                ++ "\tret\n")) (BLst [currCode, BFil filRetN]),
            codeTail
        ])

addClassElems :: Ident -> [(Ident, (Type, AttrLoc))] -> [ClassElem] -> CompilerMonad StringBuilder
addClassElems classIdent [] compileElems = do
    loc <- newLoc
    reserveRegLoc globalSelfRegLoc loc (Class Nothing classIdent) [IdentUse globalIdentSelf]
    local (first $ Data.Map.insert globalIdentSelf loc) (compileClassElems' classIdent compileElems)
addClassElems classIdent ((ident, (tp, attrLoc)):elems) compileElems = do
    case attrLoc of
        AttrLocVar depth -> do
            loc <- newLoc
            let regLoc = Mem depth globalSelfRegLoc (Lit 0) 0
            reserveRegLoc regLoc loc tp [IdentUse ident]
            local (first $ Data.Map.insert ident loc) (addClassElems classIdent elems compileElems)
        AttrLocMet depth -> do
            loc <- newLoc
            insertLocTp loc tp
            local (first $ Data.Map.insert ident loc) (addClassElems classIdent elems compileElems)

makeLabelTable' :: MethodDepth -> Data.Map.Map MethodDepth (Ident, Ident) -> CompilerMonad StringBuilder
makeLabelTable' depth mp = case Data.Map.lookup depth mp of
    Nothing -> return $ BLst []
    Just (funcIdent, originClassIdent) -> do
        tailTable <- makeLabelTable' (depth + methodDepthStep) mp
        labelF <- functionLabel' originClassIdent funcIdent
        return $ BLst [BStr $ ", " ++ labelF , tailTable]

makeLabelTable :: Ident -> CompilerMonad StringBuilder
makeLabelTable classIdent = do
    (envVar, envClass) <- ask
    case Data.Map.lookup classIdent envClass of
        Just (form, parentIdent) -> do
            let (_, methodDepthMap, _) = form
            tableCode <- makeLabelTable' 8 methodDepthMap
            return $ BLst [BStr $ classLabel classIdent ++ ": .quad " ++ classLabel classIdent, tableCode, BStr "\n"]
        Nothing -> throwError $ "class " ++ showIdent classIdent ++ " not found"

compileClassElems :: Ident -> [ClassElem] -> CompilerMonad StringBuilder
compileClassElems classIdent elems = do
    attrMap <- getAttrMap classIdent
    funcCodes <- addClassElems classIdent (Data.Map.assocs attrMap) elems
    labelTable <- makeLabelTable classIdent
    (lt, vrc, rlu, nextLabel, stackState, (dataCodes, strCount)) <- get 
    let newDataCodes = BLst [dataCodes, labelTable]
    put (lt, vrc, rlu, nextLabel, stackState, (newDataCodes, strCount))
    return $ BLst [
            funcCodes
        ]

compileTopDefs :: StringBuilder -> [TopDef] -> CompilerMonad StringBuilder
compileTopDefs code [] = do return code
compileTopDefs code ((FnDef pos tp ident args block):lst) = do
    (lt0, vrc0, rlu0, nextLabel0, stackStateOld0, strCodes0) <- get
    let maxAppArgs = digStmtInfoPub (BStmt pos block)
    (codeMov, currCode, _) <- addArgs maxAppArgs (BStmt pos block) args
    (codePush, codePop) <- stableRegsToStack
    (lt, vrc, rlu, nextLabel, (oldStack, oldStackMax), strCodes) <- get
    let stackMax = 16 * div (oldStackMax + 31) 16
    put (lt, vrc0, rlu0, nextLabel, stackStateOld0, strCodes)
    labelF <- functionLabel (IdentVar pos ident)
    compileTopDefs (BLst [
            code,
            BStr $ labelF ++ ":\n"
                ++ "\tpush %rbp\n"
                ++ "\tmovq %rsp, %rbp\n"
                ++ "\tsub $" ++ show stackMax ++ ", %rsp\n",
            codePush,
            codeMov,
            fillStringBuilder (Data.Map.singleton filRetN (
                    buildString codePop
                ++ "\tmovq %rbp, %rsp\n"
                ++ "\tpop %rbp\n"
                ++ "\tret\n")) (BLst [currCode, BFil filRetN])
        ]) lst
compileTopDefs code ((ClassDef pos ident elems):lst) = do
    (lt0, vrc0, rlu0, nextLabel0, stackStateOld0, strCodes0) <- get
    codeClass <- compileClassElems ident elems
    (lt, vrc, rlu, nextLabel, stackStateOld, strCodes) <- get
    put (lt, vrc0, rlu0, nextLabel, stackStateOld0, strCodes)
    compileTopDefs (BLst [codeClass, code]) lst
compileTopDefs code ((ClassExt pos classIdent parentIdent elems):lst) = do
    (lt0, vrc0, rlu0, nextLabel0, stackStateOld0, strCodes0) <- get
    codeClass <- compileClassElems classIdent elems
    (lt, vrc, rlu, nextLabel, stackStateOld, strCodes) <- get
    put (lt, vrc0, rlu0, nextLabel, stackStateOld0, strCodes)
    compileTopDefs (BLst [codeClass, code]) lst

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
            ++ ".globl main\n"
            ++ "main:\n"
            ++ "\tjmp fun_main\n",
        buildInCode,
        code
        ])

argsToTypes :: [Arg] -> [Type]
argsToTypes = Prelude.map argToType

extendClass :: BNFC'Position -> Ident -> Ident -> [ClassElem] -> CompilerMonad ClassForm
extendClass pos classIdent parentIdent elems = do
    (_, classEnv) <- ask
    case Data.Map.lookup parentIdent classEnv of
        Just (form,_) -> case runExcept $ formClass' classIdent form elems of
            Right formedClass -> return formedClass
            Left err -> throwError err
        Nothing -> throwError $ "Parent class " ++ showIdent parentIdent ++ " not found at: " ++ showPos pos

addEverything :: [BuiltInFunction] -> [TopDef] -> Program -> CompilerMonad String
addEverything [] [] program = compileProgram' program
addEverything [] (topDef:topDefs) program = do
    case topDef of
        FnDef pos retTp ident args block -> do
            loc <- newLoc
            let tp = Fun pos retTp (argsToTypes args)
            insertLocTp loc tp
            local (first $ Data.Map.insert ident loc) (addEverything [] topDefs program)
        ClassDef pos ident elems -> do
            loc <- newLoc
            let tp = Class pos ident
            classForm <- case runExcept $ formClass ident elems of
                Right formedClass -> return formedClass
                Left err -> throwError err
            local (Data.Bifunctor.bimap (Data.Map.insert ident loc) (Data.Map.insert ident (classForm, Ident "Object"))) (addEverything [] topDefs program)
        ClassExt pos classIdent parentIdent elems -> do
            loc <- newLoc
            classForm <- extendClass pos classIdent parentIdent elems
            local (Data.Bifunctor.bimap (Data.Map.insert classIdent loc) (Data.Map.insert classIdent (classForm, parentIdent))) (addEverything [] topDefs program)
addEverything ((ident,tp,_,_):bIFs) topDefs program = do
    loc <- newLoc
    insertLocTp loc tp
    local (first $ Data.Map.insert ident loc) (addEverything bIFs topDefs program)

compileProgram :: Program -> CompilerMonad String
compileProgram (Program pos topDefs) = addEverything builtInFunctions topDefs (Program pos topDefs)