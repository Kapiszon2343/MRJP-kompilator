module TypeChecker where

import Data.Map
import Data.Maybe (fromMaybe)
import Data.Bifunctor ( first, Bifunctor (bimap) )
import Control.Monad.State
import Control.Monad.Reader ( MonadReader(local, ask), ReaderT, asks )
import Control.Monad.Except

import Latte.Abs
import Common
    ( builtInFunctions,
      preEval,
      argToIdent,
      argToType,
      showIdent,
      showVar,
      showType,
      typePos,
      showPos,
      BuiltInFunction,
      Val(ValBool),
      Loc,
      Env,
      ClassForm,
      EnvLoc )
import qualified Latte.Abs as Data.Map

matchTypesExprs :: BNFC'Position -> [Type] -> [Expr] -> TypeCheckerMonad ()
matchTypesExprs _pos [] [] = return ()
matchTypesExprs pos (_:_) [] = throwError $ "not enough arguments at " ++ showPos pos
matchTypesExprs pos [] (_:_) = throwError $ "too many arguments at " ++ showPos pos
matchTypesExprs inPos (tp:tps) (expr:exprs) = do
    exprTp <- eval expr
    if matchType tp exprTp
        then matchTypesExprs inPos tps exprs
        else throwError $ "Mismatched types at " ++ showPos (typePos exprTp) ++ "\nExpected: " ++ showType tp ++ "\nActual: " ++ showType exprTp

matchType :: Type' a -> Type' a -> Bool
matchType (Int _) (Int _) = True
matchType (Str _) (Str _) = True
matchType (Bool _) (Bool _) = True
matchType (Void _) (Void _) = True
matchType (Fun _ ret1 []) (Fun _ ret2 []) = matchType ret1 ret2
matchType (Fun pos1 ret1 (arg1:args1)) (Fun pos2 ret2 (arg2:args2)) = 
    matchType arg1 arg2 && matchType (Fun pos1 ret1 args1) (Fun pos2 ret2 args2)
matchType (Array _ tp1) (Array _ tp2) = matchType tp1 tp2
matchType (Class _ (Ident str1)) (Class _ (Ident str2)) = str1 == str2
matchType _ _ = False

matchTypes :: Type' a -> [Type' a] -> Bool
matchTypes _ [] = True
matchTypes tpBase (tp:tail) = matchType tpBase tp && matchTypes tpBase tail

matchTypeRet :: Type -> RetType -> Bool
matchTypeRet tp1 (DoRet tp2) = matchType tp1 tp2
matchTypeRet _ NoRet = False

matchTypeBlock :: Type -> RetType -> Bool
matchTypeBlock tp1 (DoRet tp2) = matchType tp1 tp2
matchTypeBlock _ NoRet = True

confirmRetType :: Type -> RetType -> TypeCheckerMonad RetType
confirmRetType tp NoRet = return NoRet
confirmRetType tp1 (DoRet tp2) = if matchType tp1 tp2
    then return (DoRet tp1)
    else throwError ("Invalid return type: " ++ showType tp2 ++ ", Expected: " ++ showType tp1)

data RetType
    = DoRet Type
    | NoRet
type Ret = (EnvLoc -> EnvLoc, RetType)

type Mem = Data.Map.Map Loc Type
type Store = (Mem, Loc)

type TypeCheckerMonad = ExceptT String (ReaderT Env (State Store))

newloc :: TypeCheckerMonad Loc
newloc = do
    (st,l) <- get
    put (st,l+1)
    return l

modifyMem :: (Mem -> Mem) -> TypeCheckerMonad ()
modifyMem f =
    modify $ Data.Bifunctor.first f

getLoc :: BNFC'Position -> Ident -> TypeCheckerMonad Loc 
getLoc pos ident = do 
    (locs, _) <- ask
    case Data.Map.lookup ident locs of
        Nothing -> throwError $ "undefined variable at " ++ showPos pos
        Just ret -> return ret

getVarType :: Var -> TypeCheckerMonad Type
getVarType (IdentVar pos ident) = do
    loc <- getLoc pos ident
    (st,_) <- get
    case Data.Map.lookup loc st of
        Nothing -> throwError $ "undefined variable at " ++ showPos pos
        Just ret -> return ret
getVarType (ArrayVar pos var expr) = do
    arrMTp <- getVarType var
    tp <- eval expr
    case tp of
        (Int _) -> case arrMTp of
            (Array _ inTp) -> return inTp
            _ -> throwError $ "Expected " ++ showVar var ++ " to be an array, got: " ++ showType arrMTp
        _ -> throwError $ "array index has to an int, got: " ++ showType tp
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
                Just (attrMap, _) -> do
                    let attr = Data.Map.lookup ident attrMap
                    case attr of
                        Just (tp, _) -> return tp
                        Nothing -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ " does not have attribute " ++ showIdent ident
                Nothing -> throwError $ "Something went horribly wrong!!\n Could not find class " ++ showIdent classIdent ++ "of variable " ++ showVar var ++ " at: " ++ showPos pos
        _ -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ "does not have attributes"

checkFunc' ::  BNFC'Position -> EnvLoc -> Type -> [Arg] -> Block -> TypeCheckerMonad Type
checkFunc' pos blockIdent ret [] block = do
    (_, actualRet) <- typeCheckBlock ret blockIdent block
    case actualRet of
        DoRet _ -> return ret
        NoRet -> case ret of 
            (Void _) -> return ret
            _ -> throwError $ "Return value expected in function at: " ++ showPos pos
checkFunc' pos blockIdent ret (arg:args) block = do
    let tp = argToType arg
    let ident = argToIdent arg
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "arguments cannot have repeated names at: " ++ showPos pos
        Nothing -> do
            loc <- newloc
            modifyMem (Data.Map.insert loc tp)
            local (first $ Data.Map.insert ident loc) (checkFunc' pos (Data.Map.insert ident loc blockIdent) ret args block)

checkFunc :: Env -> BNFC'Position -> Type -> [Arg] -> Block -> TypeCheckerMonad Type
checkFunc env pos ret args block = do
    local (const env) (checkFunc' pos Data.Map.empty ret args block)

checkClass' :: EnvLoc -> [ClassElem] -> [ClassElem] -> TypeCheckerMonad ()
checkClass' envLoc [] [] = return ()
checkClass' envLoc [] (elem:elems) = case elem of
    Attribute pos tp ident -> checkClass' envLoc [] elems
    Method pos retTp ident args block -> do
        checkFunc' pos envLoc retTp args block
        checkClass' envLoc [] elems
checkClass' envLoc (elem:tail) elems = do
    loc <- newloc
    let ident = case elem of
            Attribute pos tp ident -> ident
            Method pos retTp ident args block -> ident
    let tp = case elem of
            Attribute pos tp ident -> tp
            Method pos retTp ident args block -> Fun pos retTp $ Prelude.foldl (\tps arg -> argToType arg:tps) [] args 
    modifyMem (Data.Map.insert loc tp)
    local (first $ Data.Map.insert ident loc) (checkClass' (Data.Map.insert ident loc envLoc) tail elems)

checkClass :: Env -> [ClassElem] -> TypeCheckerMonad ()
checkClass env elems = local (const env) (checkClass' Data.Map.empty elems elems)

makeArray :: [Expr] -> Type -> BNFC'Position -> TypeCheckerMonad Type
makeArray [] retTp _ = return retTp
makeArray (expr:tail) retTp pos = do
    tp <- eval expr
    case tp of
        (Int _) -> do
            innerTp <- makeArray tail retTp pos
            return (Array pos innerTp)
        _ -> throwError $ "Wrong type of array size at: " ++ showPos pos ++ "\nExpected: Int\nActual: " ++ showType tp

evalArr :: [Expr] -> TypeCheckerMonad [Type]
evalArr [] = return []
evalArr (expr:tail) = do
    tp <- eval expr
    tpTail <- evalArr tail
    return (tp:tpTail)

eval :: Expr -> TypeCheckerMonad Type
eval (EVar pos var) = do
    getVarType var
eval (ENew pos new) =
    case new of
        NewBase _ baseTp -> return baseTp
        NewArray posArr newBase expr -> do
            lenTp <- eval expr
            case lenTp of
                Int _ -> do
                    baseTp <- eval (ENew pos newBase)
                    return $ Array posArr baseTp
                _ -> throwError $ "Wrong parameter at: " ++ showPos posArr ++ "\nExpected int\nActual: " ++ showType lenTp
eval (ELitArr pos []) = throwError $ "Cannot initialize empty array due to ambiguous type at: " ++ showPos pos
eval (ELitArr pos (expr:tail)) = do
    tpBase <- eval expr
    tpTail <- evalArr tail
    if matchTypes tpBase tpTail
        then return (Array pos tpBase)
        else throwError $ "Array elements need to have the same type at: " ++ showPos pos
eval (ELitInt pos integer) = return (Int pos)
eval (ELitTrue pos) = return (Bool pos)
eval (ELitFalse pos) = return (Bool pos)
eval (ELitNull pos ident) = return (Class pos ident) -- TODO check if class exists
eval (EApp pos var params) =  do
    func <- getVarType var
    case func of
        (Fun fPos ret args) -> do 
            matchTypesExprs pos args params
            return ret
        _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected function\nActual: " ++ showType func
eval (EString pos string) = return (Str pos)
eval (Neg pos expr) = do
    tp <- eval expr
    if matchType tp (Int pos)
        then return (Int pos)
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp
eval (Not pos expr) = do
    tp <- eval expr
    if matchType tp (Bool pos)
        then return (Bool pos)
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp
eval (EMul pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    if matchType tp1 (Int pos)
        then if matchType tp2 (Int pos)
            then return (Int pos)
            else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp1
eval (EAdd pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    case op of
        (Plus _) -> case tp1 of
            (Int _) -> if matchType tp2 (Int pos)
                then return (Int pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
            (Str _) -> if matchType tp2 (Str pos)
                    then return (Str pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: string\nActual: " ++ showType tp2
            _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int or string\nActual: " ++ showType tp1
        (Minus _) -> case tp1 of
            (Int _) -> if matchType tp2 (Int pos)
                then return (Int pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
            (Str _) -> if matchType tp2 (Str pos)
                    then return (Str pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
            _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp1
eval (ERel pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    case tp1 of
        (Int _) -> if matchType tp2 (Int pos)
            then return (Bool pos)
            else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
        _ -> case op of
            (EQU _) -> if matchType tp1 tp2
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: " ++ showType tp1 ++ "\nActual: " ++ showType tp2
            (NE _) -> if matchType tp1 tp2
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: " ++ showType tp1 ++ "\nActual: " ++ showType tp2
            _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp2
eval (EAnd pos expr1 expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    if matchType tp1 (Bool pos)
        then if matchType tp2 (Bool pos)
            then return (Bool pos)
            else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp2
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp1
eval (EOr pos expr1 expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    if matchType tp1 (Bool pos)
        then if matchType tp2 (Bool pos)
            then return (Bool pos)
            else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp2
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp1

evalItems :: EnvLoc -> Type -> [Item] -> TypeCheckerMonad [(Ident, Loc)]
evalItems _blockIdent _def [] = return []
evalItems blockIdent tp ((NoInit pos ident):items) = do
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "Multiple definitions of same name at: " ++ showPos pos
        Nothing -> do
            loc <- newloc
            rets <- evalItems (Data.Map.insert ident loc blockIdent) tp items
            modifyMem (Data.Map.insert loc tp)
            return $ (ident, loc):rets
evalItems blockIdent tp ((Init pos ident expr):items) = do
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "Multiple definitions of same name at: " ++ showPos pos
        Nothing -> do
            evalTp <- eval expr
            if matchType tp evalTp
                then do
                    loc <- newloc
                    rets <- evalItems (Data.Map.insert ident loc blockIdent) tp items
                    modifyMem (Data.Map.insert loc tp)
                    return $ (ident, loc):rets
                else throwError $ "Wrong assign type at: " ++ showPos pos ++ "\nExpected: " ++ showType evalTp ++ "\nActual: " ++ showType tp

typeCheckBlock' :: RetType -> Type -> EnvLoc -> Block -> TypeCheckerMonad Ret 
typeCheckBlock' ret expectedTyp _ (Block _ []) = do return (id, ret)
typeCheckBlock' ret expectedType blockIdent (Block pos (stmt:block)) = do
    (envLocMod, newRet) <- typeCheck expectedType blockIdent stmt
    let envMod (envLoc, envClass) = (envLocMod envLoc, envClass)
    case ret of
        NoRet -> local envMod (typeCheckBlock' newRet expectedType (envLocMod blockIdent) (Block pos block))
        DoRet _ -> local envMod (typeCheckBlock' ret expectedType (envLocMod blockIdent) (Block pos block))

typeCheckBlock :: Type -> EnvLoc -> Block -> TypeCheckerMonad Ret 
typeCheckBlock = typeCheckBlock' NoRet

typeCheck :: Type -> EnvLoc -> Stmt -> TypeCheckerMonad Ret
typeCheck expectedType _ (Empty pos) = do return (id, NoRet)
typeCheck expectedType _ (BStmt bStmtPos block) = 
    typeCheckBlock expectedType Data.Map.empty block
typeCheck expectedType blockIdent (Decl pos valType items) = do
    vals <- evalItems blockIdent valType items
    return (\env -> Prelude.foldl (\ mp (ident, loc) -> Data.Map.insert ident loc mp) env vals, NoRet)
typeCheck expectedType _ (Ass pos var expr) = do 
    exprTp <- eval expr
    tp <- getVarType var
    if matchType tp exprTp
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType tp ++ "\nActual: " ++ showType exprTp
typeCheck expectedType _ (Incr pos var) = do 
    tp <- getVarType var
    if matchType tp (Int pos)
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType _ (Decr pos var) = do 
    tp <- getVarType var
    if matchType tp (Int pos)
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType _ (Ret pos expr) = do 
    tp <- eval expr
    if matchType tp expectedType
        then return (id, DoRet tp)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType _ (VRet pos) = if matchType (Void pos) expectedType
        then return (id, DoRet (Void pos))
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: Void"
typeCheck expectedType blockIdent (Cond pos expr stmtTrue) = do
    tp <- eval expr
    if matchType tp (Bool pos)
        then do
            (_, retTrue) <- typeCheck expectedType blockIdent stmtTrue
            case preEval expr of
                ValBool True -> return (id, retTrue)
                _ -> return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType blockIdent (CondElse pos expr stmtTrue stmtFalse) = do
    tp <- eval expr
    if matchType tp (Bool pos)
        then do 
            (_, retTrue) <- typeCheck expectedType blockIdent stmtTrue
            (_, retFalse) <- typeCheck expectedType blockIdent stmtFalse
            case preEval expr of
                ValBool True -> return (id, retTrue)
                ValBool False -> return (id, retFalse)
                _ -> case retTrue of
                    NoRet -> return (id, NoRet)
                    (DoRet _) -> return (id, retFalse)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType blockIdent (While pos expr loopStmt) = do
    tpCond <- eval expr
    case tpCond of
        Bool _ -> typeCheck expectedType blockIdent loopStmt
        _ -> throwError $ "Wrong expression type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tpCond
typeCheck expectedType _ (For pos valType ident exprSet exprCond incrStmt loopStmt) = do
    iterLoc <- newloc
    iterLoc <- newloc
    modifyMem $ Data.Map.insert iterLoc valType
    tpSet <- eval exprSet
    if matchType tpSet valType 
        then do
            tpCond <- local (first $ Data.Map.insert ident iterLoc) (eval exprCond)
            if matchType tpCond (Bool Nothing)
                then do
                    local (first $ Data.Map.insert ident iterLoc) 
                        (typeCheck expectedType (Data.Map.insert ident iterLoc Data.Map.empty) incrStmt)
                    local (first $ Data.Map.insert ident iterLoc) 
                        (typeCheck expectedType (Data.Map.insert ident iterLoc Data.Map.empty) loopStmt)
                else throwError $ "Wrong expression type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tpCond
        else throwError $ "Wrong expression type at: " ++ showPos pos ++ "\nExpected: " ++ showType valType ++ "\nActual: " ++ showType tpSet
typeCheck expectedType _ (ForEach pos valType ident expr loopStmt) = do
    val <- eval expr
    case val of
        (Array _ tp) -> if matchType tp valType
            then do
                loc <- newloc
                modifyMem $ Data.Map.insert loc valType
                local (first $ Data.Map.insert ident loc) 
                    (typeCheck expectedType (Data.Map.insert ident loc Data.Map.empty) loopStmt)
            else throwError $ "Created type does not match assignment at: " ++ showPos pos ++ "\tExpected: " ++ showType valType ++ "\nActual: " ++ showType tp
        _ -> throwError $ "Foreach requires array to iterate through at: " ++ showPos pos
typeCheck expectedType _ (SExp pos expr) = do
    eval expr
    return (id, NoRet)

runTopDefs :: [TopDef] -> TypeCheckerMonad (IO ())
runTopDefs [] = do 
    return $ putStrLn "types checker finished successfully"  
runTopDefs ((FnDef pos ret ident args block):tail) = do
    env <- ask
    checkFunc env pos ret args block
    runTopDefs tail
runTopDefs ((ClassDef pos ident elems):tail) = do
    env <- ask
    checkClass env elems 
    runTopDefs tail

formClass :: [ClassElem] -> TypeCheckerMonad ClassForm
formClass [] = return (Data.Map.empty, 0)
formClass (elem:elems) = do
    (attrMap, size) <- formClass elems
    case elem of
        Attribute pos tp ident -> case Data.Map.lookup ident attrMap of
            Just _ -> throwError $ "Multiple definitions of: " ++ showIdent ident ++ "  at: " ++ showPos pos
            Nothing -> return (Data.Map.insert ident (tp, 4) attrMap, size + 4)
        Method pos retTp ident args block -> case Data.Map.lookup ident attrMap of
            Just _ -> throwError $ "Multiple definitions of: " ++ showIdent ident ++ "  at: " ++ showPos pos
            Nothing -> return (
                Data.Map.insert ident (Fun pos retTp $ Prelude.foldl (\tps arg -> argToType arg:tps) [] args, 4) attrMap, 
                size + 4)

addTopDefs :: [TopDef] -> [TopDef] -> TypeCheckerMonad (IO ())
addTopDefs [] topDefs2 = runTopDefs topDefs2
addTopDefs ((FnDef pos ret ident args _block):lst) topDefs2 = do
    (envLoc, envClass) <- ask
    case Data.Map.lookup ident envLoc of
        Just _ -> throwError $ "Multiple definitions of: " ++ showIdent ident ++ "  at: " ++ showPos pos
        Nothing -> do
            loc <- newloc
            modifyMem (Data.Map.insert loc (Fun pos ret (Prelude.map argToType args)))
            local (first $ Data.Map.insert ident loc) (addTopDefs lst topDefs2)
addTopDefs ((ClassDef pos ident elems):lst) topDefs2 = do
    (envLoc, envClass) <- ask
    case Data.Map.lookup ident envLoc of
        Just _ -> throwError $ "Multiple definitions of: " ++ showIdent ident ++ "  at: " ++ showPos pos
        Nothing -> do
            loc <- newloc
            modifyMem (Data.Map.insert loc (Class pos ident))
            classForm <- formClass elems
            local (Data.Bifunctor.bimap (Data.Map.insert ident loc) (Data.Map.insert ident classForm)) (addTopDefs lst topDefs2)

addBuildIntFunctions :: [BuiltInFunction] -> Program -> TypeCheckerMonad (IO ())
addBuildIntFunctions [] (Program pos topDefs) = addTopDefs topDefs topDefs
addBuildIntFunctions ((ident, tp, _):functions) program = do
    env <- ask
    loc <- newloc
    modifyMem (Data.Map.insert loc tp)
    local (first $ Data.Map.insert ident loc) (addBuildIntFunctions functions program)

typeCheckProgram :: Program -> TypeCheckerMonad (IO ())
typeCheckProgram = addBuildIntFunctions builtInFunctions