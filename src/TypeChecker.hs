module TypeChecker where

import Data.Map
import Data.Maybe (fromMaybe)
import Data.Bifunctor ( first, Bifunctor (bimap) )
import Control.Monad.State
import Control.Monad.Reader
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
      EnvLoc, formClass', formClass )
import qualified Latte.Abs as Data.Map
import Data.Bool (bool)
import Data.Array (Array)

matchTypesExprs :: BNFC'Position -> [Type] -> [Expr] -> TypeCheckerMonad ()
matchTypesExprs _pos [] [] = return ()
matchTypesExprs pos (_:_) [] = throwError $ "not enough arguments at " ++ showPos pos
matchTypesExprs pos [] (_:_) = throwError $ "too many arguments at " ++ showPos pos
matchTypesExprs inPos (tp:tps) (expr:exprs) = do
    exprTp <- eval expr
    bol <- matchType tp exprTp
    if bol
        then matchTypesExprs inPos tps exprs
        else throwError $ "Mismatched types at " ++ showPos (typePos exprTp) ++ "\nExpected: " ++ showType tp ++ "\nActual: " ++ showType exprTp

matchType :: Type' a -> Type' a -> TypeCheckerMonad Bool
matchType (Int _) (Int _) = return True
matchType (Str _) (Str _) = return True
matchType (Bool _) (Bool _) = return True
matchType (Void _) (Void _) = return True
matchType (Fun _ ret1 []) (Fun _ ret2 []) = matchType ret1 ret2
matchType (Fun pos1 ret1 (arg1:args1)) (Fun pos2 ret2 (arg2:args2)) = do
    argBol <- matchType arg1 arg2 
    if argBol 
        then matchType (Fun pos1 ret1 args1) (Fun pos2 ret2 args2)
        else return False
matchType (Array _ tp1) (Array _ tp2) = matchType tp1 tp2
matchType (Class pos1 (Ident str1)) (Class pos2 (Ident str2)) =
    if str1 == str2
        then return True
        else do
            (_, classEnv) <- ask
            case Data.Map.lookup (Ident str2) classEnv of
                Just (_, parentIdent) -> matchType (Class pos1 (Ident str1)) (Class pos2 parentIdent)
                Nothing -> return False
matchType _ _ = return False

matchTypes :: Type' a -> [Type' a] -> TypeCheckerMonad Bool
matchTypes _ [] = return True
matchTypes tpBase (tp:tail) = do
    bol <- matchType tpBase tp 
    if bol
        then matchTypes tpBase tail
        else return False

matchTypeRet :: Type -> RetType -> TypeCheckerMonad Bool
matchTypeRet tp1 (DoRet tp2) = matchType tp1 tp2
matchTypeRet _ NoRet = return False

matchTypeBlock :: Type -> RetType -> TypeCheckerMonad Bool
matchTypeBlock tp1 (DoRet tp2) = matchType tp1 tp2
matchTypeBlock _ NoRet = return True

confirmRetType :: Type -> RetType -> TypeCheckerMonad RetType
confirmRetType tp NoRet = return NoRet
confirmRetType tp1 (DoRet tp2) = do
    bol <- matchType tp1 tp2
    if bol
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
                Just ((attrMap, _, _),_) -> do
                    let attr = Data.Map.lookup ident attrMap
                    case attr of
                        Just (tp, _) -> return tp
                        Nothing -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ " does not have attribute " ++ showIdent ident
                Nothing -> throwError $ "Something went horribly wrong!!\n Could not find class " ++ showIdent classIdent ++ "of variable " ++ showVar var ++ " at: " ++ showPos pos
        _ -> throwError $ "Wrong attribute at: " ++ showPos pos ++ "\nType " ++ showType baseTp ++ "does not have attributes"

failOnVoid :: Type -> TypeCheckerMonad ()
failOnVoid (Void pos) = throwError $ "Type 'void' is not allowed at: " ++ showPos pos
failOnVoid (Array pos baseTp) = failOnVoid baseTp
failOnVoid _ = return ()

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
    failOnVoid tp
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

checkClass :: Env -> Ident -> [ClassElem] -> TypeCheckerMonad ()
checkClass env ident elems = do
    loc <- newloc
    modifyMem (Data.Map.insert loc (Class Nothing ident))
    local (const (first (Data.Map.insert (Ident "self") loc) env)) (checkClass' (Data.Map.singleton (Ident "self") loc) elems elems)

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
    bol <- matchTypes tpBase tpTail
    if bol
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
eval (ENeg pos expr) = do
    tp <- eval expr
    bol <- matchType tp (Int pos)
    if bol
        then return (Int pos)
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp
eval (ENot pos expr) = do
    tp <- eval expr
    bol <- matchType tp (Bool pos)
    if bol
        then return (Bool pos)
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp
eval (EMul pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    bol1 <- matchType tp1 (Int pos)
    if bol1
        then do
            bol2 <- matchType tp2 (Int pos)
            if bol2
                then return (Int pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp1
eval (EAdd pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    case op of
        (Plus _) -> case tp1 of
            (Int _) -> do 
                bol <- matchType tp2 (Int pos)
                if bol
                    then return (Int pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
            (Str _) -> do
                bol <- matchType tp2 (Str pos)
                if bol
                    then return (Str pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: string\nActual: " ++ showType tp2
            _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int or string\nActual: " ++ showType tp1
        (Minus _) -> case tp1 of
            (Int _) -> do
                bol <- matchType tp2 (Int pos)
                if bol
                    then return (Int pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
            (Str _) -> do 
                bol <- matchType tp2 (Str pos)
                if bol
                    then return (Str pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
            _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp1
eval (ERel pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    case tp1 of
        (Int _) -> do 
            bol <- matchType tp2 (Int pos)
            if bol
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: int\nActual: " ++ showType tp2
        _ -> case op of
            (EQU _) -> do 
                bol <- matchType tp1 tp2
                if bol
                    then return (Bool pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: " ++ showType tp1 ++ "\nActual: " ++ showType tp2
            (NE _) -> do 
                bol <- matchType tp1 tp2
                if bol
                    then return (Bool pos)
                    else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: " ++ showType tp1 ++ "\nActual: " ++ showType tp2
            _ -> throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp2
eval (EAnd pos expr1 expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    bol1 <- matchType tp1 (Bool pos)
    if bol1
        then do 
            bol2 <- matchType tp2 (Bool pos)
            if bol2
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp2
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp1
eval (EOr pos expr1 expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    bol1 <- matchType tp1 (Bool pos)
    if bol1
        then do 
            bol2 <- matchType tp2 (Bool pos)
            if bol2
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp2
        else throwError $ "Wrong parameter type at: " ++ showPos pos ++ "\nExpected: bool\nActual: " ++ showType tp1

evalItems :: EnvLoc -> Type -> [Item] -> TypeCheckerMonad (EnvLoc -> EnvLoc)
evalItems _blockIdent _def [] = return id
evalItems blockIdent tp ((NoInit pos ident):items) = do
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "Multiple definitions of same name at: " ++ showPos pos
        Nothing -> do
            loc <- newloc
            modifyMem (Data.Map.insert loc tp)
            let envLocMod1 = Data.Map.insert ident loc
            envLocMod2 <- local (first envLocMod1) (evalItems (Data.Map.insert ident loc blockIdent) tp items)
            return $ envLocMod1 . envLocMod2
evalItems blockIdent tp ((Init pos ident expr):items) = do
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "Multiple definitions of same name at: " ++ showPos pos
        Nothing -> do
            evalTp <- eval expr
            bol <- matchType tp evalTp
            if bol
                then do
                    loc <- newloc
                    modifyMem (Data.Map.insert loc tp)
                    let envLocMod1 = Data.Map.insert ident loc
                    envLocMod2 <- local (first envLocMod1) (evalItems (Data.Map.insert ident loc blockIdent) tp items)
                    return $ envLocMod1 . envLocMod2
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
    failOnVoid valType
    envMod <- evalItems blockIdent valType items
    return (envMod, NoRet)
typeCheck expectedType _ (Ass pos var expr) = do 
    exprTp <- eval expr
    tp <- getVarType var
    bol <- matchType tp exprTp
    if bol
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType tp ++ "\nActual: " ++ showType exprTp
typeCheck expectedType _ (Incr pos var) = do 
    tp <- getVarType var
    bol <- matchType tp (Int pos)
    if bol
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType _ (Decr pos var) = do 
    tp <- getVarType var
    bol <- matchType tp (Int pos)
    if bol
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType _ (Ret pos expr) = do 
    tp <- eval expr
    bol <- matchType tp expectedType
    if bol
        then return (id, DoRet tp)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType _ (VRet pos) = do 
    bol <- matchType (Void pos) expectedType
    if bol
        then return (id, DoRet (Void pos))
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: Void"
typeCheck expectedType blockIdent (Cond pos expr stmtTrue) = do
    tp <- eval expr
    bol <- matchType tp (Bool pos)
    if bol
        then do
            (_, retTrue) <- typeCheck expectedType blockIdent stmtTrue
            case preEval expr of
                ValBool True -> return (id, retTrue)
                _ -> return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ showPos pos ++ "\nExpected: " ++ showType expectedType ++ "\nActual: " ++ showType tp
typeCheck expectedType blockIdent (CondElse pos expr stmtTrue stmtFalse) = do
    tp <- eval expr
    bol <- matchType tp (Bool pos)
    if bol
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
    bol1 <- matchType tpSet valType
    if bol1 
        then do
            tpCond <- local (first $ Data.Map.insert ident iterLoc) (eval exprCond)
            bol2 <- matchType tpCond (Bool Nothing)
            if bol2
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
        (Array _ tp) -> do
            bol <- matchType tp valType
            if bol
                then do
                    loc <- newloc
                    modifyMem $ Data.Map.insert loc valType
                    local (first $ Data.Map.insert ident loc) 
                        (typeCheck expectedType (Data.Map.insert ident loc Data.Map.empty) loopStmt)
                else throwError $ "Created type does not match assignment at: " ++ showPos pos ++ "\tExpected: " ++ showType valType ++ "\nActual: " ++ showType tp
        _ -> throwError $ "Foreach requires array to iterate through at: " ++ showPos pos
typeCheck expectedType _ (SExp pos expr) = do
    eval expr
    case expr of
        (EApp posApp (IdentVar posVar ident) args) -> if ident == Ident "error"
            then return (id, DoRet expectedType)
            else return (id, NoRet)
        _ -> return (id, NoRet)

runTopDefs :: [TopDef] -> TypeCheckerMonad (IO ())
runTopDefs [] = do 
    return $ putStrLn "types checker finished successfully"  
runTopDefs ((FnDef pos ret ident args block):tail) = do
    env <- ask
    checkFunc env pos ret args block
    runTopDefs tail
runTopDefs ((ClassDef pos ident elems):tail) = do
    env <- ask
    checkClass env ident elems 
    runTopDefs tail
runTopDefs ((ClassExt pos classIdent _parentIdent elems):tail) = do
    env <- ask
    checkClass env classIdent elems 
    runTopDefs tail

extendClass :: BNFC'Position -> Ident -> Ident -> [ClassElem] -> TypeCheckerMonad ClassForm
extendClass pos classIdent parentIdent elems = do
    (_, classEnv) <- ask
    case Data.Map.lookup parentIdent classEnv of
        Just (form,_) -> case runExcept $ formClass' classIdent form elems of
            Right formedClass -> return formedClass
            Left err -> throwError err
        Nothing -> throwError $ "Parent class " ++ showIdent parentIdent ++ " not found at: " ++ showPos pos

addTopDefs :: [TopDef] -> [TopDef] -> TypeCheckerMonad (IO ())
addTopDefs [] topDefs2 = do
    (envLoc, envClass) <- ask
    case Data.Map.lookup (Ident "main") envLoc of
        Just loc -> do
            (mem, _) <- get
            case Data.Map.lookup loc mem of
                Just (Fun pos retTp []) -> do
                    isTypeSame <- matchType retTp (Int pos)
                    if isTypeSame
                        then runTopDefs topDefs2
                        else throwError "function \"main\" should return int"
                Just (Fun _ retTp _) -> throwError "function \"main\" should not have arguments"
                _ -> throwError "function \"main\" has wrong type"
        Nothing -> throwError "function \"main\" has not been implemented"
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
            classForm <- case runExcept $ formClass ident elems of
                Right formedClass -> return formedClass
                Left err -> throwError err
            local (Data.Bifunctor.bimap (Data.Map.insert ident loc) (Data.Map.insert ident (classForm, Ident ""))) (addTopDefs lst topDefs2)
addTopDefs ((ClassExt pos classIdent parentIdent elems):lst) topDefs2 = do
    (envLoc, envClass) <- ask
    case Data.Map.lookup classIdent envLoc of
        Just _ -> throwError $ "Multiple definitions of: " ++ showIdent classIdent ++ "  at: " ++ showPos pos
        Nothing -> do
            loc <- newloc
            modifyMem (Data.Map.insert loc (Class pos classIdent))
            classForm <- extendClass pos classIdent parentIdent elems
            local (Data.Bifunctor.bimap (Data.Map.insert classIdent loc) (Data.Map.insert classIdent (classForm, parentIdent))) (addTopDefs lst topDefs2)

addBuildIntFunctions :: [BuiltInFunction] -> Program -> TypeCheckerMonad (IO ())
addBuildIntFunctions [] (Program pos topDefs) = addTopDefs topDefs topDefs
addBuildIntFunctions ((ident, tp, _, _):functions) program = do
    env <- ask
    loc <- newloc
    modifyMem (Data.Map.insert loc tp)
    local (first $ Data.Map.insert ident loc) (addBuildIntFunctions functions program)

typeCheckProgram :: Program -> Either String (IO ())
typeCheckProgram program = evalState (runReaderT (runExceptT $ addBuildIntFunctions builtInFunctions program) (Data.Map.singleton (Ident "self") 0, Data.Map.empty)) (Data.Map.empty, 1)