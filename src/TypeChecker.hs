module TypeChecker where

import Data.Map
import Data.Maybe (fromMaybe)
import Data.Bifunctor ( first )
import Control.Monad.State
import Control.Monad.Reader ( MonadReader(local, ask), ReaderT, asks )
import Control.Monad.Except

import Latte.Abs
import Common
import qualified Latte.Abs as Data.Map

matchTypesExprs :: BNFC'Position -> [Type] -> [Expr] -> TypeCheckerMonad ()
matchTypesExprs _pos [] [] = return ()
matchTypesExprs pos (_:_) [] = throwError $ "not enough arguments at " ++ posToStr pos
matchTypesExprs pos [] (_:_) = throwError $ "too many arguments at " ++ posToStr pos
matchTypesExprs inPos (tp:tps) (expr:exprs) = do
    exprTp <- eval expr
    if matchType tp exprTp
        then matchTypesExprs inPos tps exprs
        else throwError $ "Mismatched types at " ++ show (typePos tp) ++ "\nExpected: " ++ show tp ++ "\nActual: " ++ "show expr"

matchType :: Type' a -> Type' a -> Bool
matchType (Int _) (Int _) = True
matchType (Str _) (Str _) = True
matchType (Bool _) (Bool _) = True
matchType (Void _) (Void _) = True
matchType (Fun _ ret1 []) (Fun _ ret2 []) = matchType ret1 ret2
matchType (Fun pos1 ret1 (arg1:args1)) (Fun pos2 ret2 (arg2:args2)) = 
    matchType arg1 arg2 && matchType (Fun pos1 ret1 args1) (Fun pos2 ret2 args2)
matchType (Array _ tp1) (Array _ tp2) = matchType tp1 tp2
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
    else throwError ("Invalid return type: " ++ show tp2 ++ ", Expected: " ++ show tp1)

data RetType
    = DoRet Type
    | NoRet
type Ret = (Env -> Env, RetType)

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
    env <- ask
    case Data.Map.lookup ident env of
        Nothing -> throwError $ "undefined variable at " ++ posToStr pos
        Just ret -> return ret

getVarType :: Var -> TypeCheckerMonad Type
getVarType (IdentVar pos ident) = do
    loc <- getLoc pos ident
    (st,_) <- get
    case Data.Map.lookup loc st of
        Nothing -> throwError $ "undefined variable at " ++ posToStr pos
        Just ret -> return ret
getVarType (ArrayVar pos var expr) = do
    arrMTp <- getVarType var
    tp <- eval expr
    case tp of
        (Int _) -> case arrMTp of
            (Array _ inTp) -> return inTp
            _ -> throwError $ "Expected " ++ show var ++ " to be an array, got: " ++ show arrMTp
        _ -> throwError $ "array index has to an int, got: " ++ show tp

checkFunc' ::  BNFC'Position -> Env -> Type -> [Arg] -> Block -> TypeCheckerMonad Type
checkFunc' pos blockIdent ret [] block = do
    (_, actualRet) <- typeCheckBlock ret blockIdent block
    case actualRet of
        DoRet _ -> return ret
        NoRet -> case ret of 
            (Void _) -> return ret
            _ -> throwError $ "Return value expected in function at: " ++ posToStr pos
checkFunc' pos blockIdent ret (arg:args) block = do
    let tp = argToType arg
    let ident = argToIdent arg
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "arguments cannot have repeated names at: " ++ posToStr pos
        Nothing -> do
            loc <- newloc
            modifyMem (Data.Map.insert loc tp)
            local (Data.Map.insert ident loc) (checkFunc' pos (Data.Map.insert ident loc blockIdent) ret args block)

checkFunc :: Env -> BNFC'Position -> Type -> [Arg] -> Block -> TypeCheckerMonad Type
checkFunc env pos ret args block = do
    local (const env) (checkFunc' pos Data.Map.empty ret args block)
    
makeArray :: [Expr] -> Type -> BNFC'Position -> TypeCheckerMonad Type
makeArray [] retTp _ = return retTp
makeArray (expr:tail) retTp pos = do
    tp <- eval expr
    case tp of
        (Int _) -> do
            innerTp <- makeArray tail retTp pos
            return (Array pos innerTp)
        _ -> throwError $ "Wrong type of array size at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp

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
    throwError "unimplemented"
    -- makeArray exprArr valType pos
eval (ELitArr pos []) = throwError $ "Cannot initialize empty array due to ambiguous type at: " ++ posToStr pos
eval (ELitArr pos (expr:tail)) = do
    tpBase <- eval expr
    tpTail <- evalArr tail
    if matchTypes tpBase tpTail
        then return (Array pos tpBase)
        else throwError $ "Array elements need to have the same type at: " ++ posToStr pos
eval (ELitInt pos integer) = return (Int pos)
eval (ELitTrue pos) = return (Bool pos)
eval (ELitFalse pos) = return (Bool pos)
eval (EApp pos var params) =  do
    func <- getVarType var
    case func of
        (Fun fPos ret args) -> do 
            matchTypesExprs pos args params
            return ret
        _ -> throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected function\nActual: " ++ show func
eval (EString pos string) = return (Str pos)
eval (Neg pos expr) = do
    tp <- eval expr
    if matchType tp (Int pos)
        then return (Int pos)
        else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp
eval (Not pos expr) = do
    tp <- eval expr
    if matchType tp (Bool pos)
        then return (Bool pos)
        else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp
eval (EMul pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    if matchType tp1 (Int pos)
        then if matchType tp2 (Int pos)
            then return (Int pos)
            else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp2
        else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp1
eval (EAdd pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    case op of
        (Plus _) -> case tp1 of
            (Int _) -> if matchType tp2 (Int pos)
                then return (Int pos)
                else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp2
            (Str _) -> if matchType tp2 (Str pos)
                    then return (Str pos)
                    else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp2
            _ -> throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int or String\nActual: " ++ show tp1
        (Minus _) -> case tp1 of
            (Int _) -> if matchType tp2 (Int pos)
                then return (Int pos)
                else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp2
            (Str _) -> if matchType tp2 (Str pos)
                    then return (Str pos)
                    else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp2
            _ -> throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp1
eval (ERel pos expr1 op expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    case tp1 of
        (Int _) -> if matchType tp2 (Int pos)
            then return (Bool pos)
            else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int\nActual: " ++ show tp2
        (Bool _) -> case op of
            (EQU _) -> if matchType tp2 (Bool pos)
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp2
            (NE _) -> if matchType tp2 (Bool pos)
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp2
            _ -> throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp2
        (Str _) -> case op of
            (EQU _) -> if matchType tp2 (Str pos)
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Str\nActual: " ++ show tp2
            (NE _) -> if matchType tp2 (Str pos)
                then return (Bool pos)
                else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Str\nActual: " ++ show tp2
            _ -> throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Str\nActual: " ++ show tp2
        _ -> throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Int, Bool or String\nActual: " ++ show tp2
eval (EAnd pos expr1 expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    if matchType tp1 (Bool pos)
        then if matchType tp2 (Bool pos)
            then return (Bool pos)
            else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp2
        else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp1
eval (EOr pos expr1 expr2) = do
    tp1 <- eval expr1
    tp2 <- eval expr2
    if matchType tp1 (Bool pos)
        then if matchType tp2 (Bool pos)
            then return (Bool pos)
            else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp2
        else throwError $ "Wrong parameter type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tp1

evalItems :: Env -> Type -> [Item] -> TypeCheckerMonad [(Ident, Loc)]
evalItems _blockIdent _def [] = return []
evalItems blockIdent tp ((NoInit pos ident):items) = do
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "Multiple definitions of same name at: " ++ posToStr pos
        Nothing -> do
            loc <- newloc
            rets <- evalItems (Data.Map.insert ident loc blockIdent) tp items
            modifyMem (Data.Map.insert loc tp)
            return $ (ident, loc):rets
evalItems blockIdent tp ((Init pos ident expr):items) = do
    case Data.Map.lookup ident blockIdent of
        Just _ -> throwError $ "Multiple definitions of same name at: " ++ posToStr pos
        Nothing -> do
            evalTp <- eval expr
            if matchType tp $ evalTp
                then do
                    loc <- newloc
                    rets <- evalItems (Data.Map.insert ident loc blockIdent) tp items
                    modifyMem (Data.Map.insert loc tp)
                    return $ (ident, loc):rets
                else throwError $ "Wrong assign type at: " ++ posToStr pos ++ "\nExpected: " ++ show evalTp ++ "\nActual: " ++ show tp

typeCheckBlock' :: Type -> RetType -> Env -> Block -> TypeCheckerMonad Ret 
typeCheckBlock' expectedType ret _ (Block _ []) = do return (id, ret)
typeCheckBlock' expectedType ret blockIdent (Block pos (stmt:block)) = do
    (envMod, newRet) <- typeCheck expectedType blockIdent stmt
    case ret of
        NoRet -> local envMod (typeCheckBlock' expectedType newRet (envMod blockIdent) (Block pos block))
        DoRet _ -> local envMod (typeCheckBlock' expectedType ret (envMod blockIdent) (Block pos block))

typeCheckBlock :: Type -> Env -> Block -> TypeCheckerMonad Ret 
typeCheckBlock expectedType _ (Block _ []) = do return (id, NoRet)
typeCheckBlock expectedType blockIdent (Block pos (stmt:block)) = do
    (envMod, ret) <- typeCheck expectedType blockIdent stmt
    local envMod (typeCheckBlock expectedType (envMod blockIdent) (Block pos block))

typeCheck :: Type -> Env -> Stmt -> TypeCheckerMonad Ret
typeCheck expectedType _ (Empty pos) = do return (id, NoRet)
typeCheck expectedType _ (BStmt bStmtPos block) = 
    typeCheckBlock expectedType Data.Map.empty block
typeCheck expectedType blockIdent (Decl pos valType items) = do
    vals <- evalItems blockIdent valType items
    return (\env -> Prelude.foldl (\ mp (ident, loc) -> Data.Map.insert ident loc mp) env vals, NoRet)
typeCheck expectedType _ (Ass pos ident expr) = do 
    exprTp <- eval expr
    tp <- getVarType (IdentVar pos ident)
    if matchType tp exprTp
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ posToStr pos ++ "\nExpected: " ++ show tp ++ "\nActual: " ++ show exprTp
typeCheck expectedType _ (Incr pos ident) = do 
    tp <- getVarType (IdentVar pos ident)
    if matchType tp (Int pos)
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ posToStr pos ++ "\nExpected: " ++ show expectedType ++ "\nActual: " ++ show tp
typeCheck expectedType _ (Decr pos ident) = do 
    tp <- getVarType (IdentVar pos ident)
    if matchType tp (Int pos)
        then return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ posToStr pos ++ "\nExpected: " ++ show expectedType ++ "\nActual: " ++ show tp
typeCheck expectedType _ (Ret pos expr) = do 
    tp <- eval expr
    if matchType tp expectedType
        then return (id, DoRet tp)
        else throwError $ "Wrong return type at: " ++ posToStr pos ++ "\nExpected: " ++ show expectedType ++ "\nActual: " ++ show tp
typeCheck expectedType _ (VRet pos) = if matchType (Void pos) expectedType
        then return (id, DoRet (Void pos))
        else throwError $ "Wrong return type at: " ++ posToStr pos ++ "\nExpected: " ++ show expectedType ++ "\nActual: Void"
typeCheck expectedType blockIdent (Cond pos expr stmtTrue) = do
    tp <- eval expr
    if matchType tp (Bool pos)
        then do
            typeCheck expectedType blockIdent stmtTrue
            return (id, NoRet)
        else throwError $ "Wrong return type at: " ++ posToStr pos ++ "\nExpected: " ++ show expectedType ++ "\nActual: " ++ show tp
typeCheck expectedType blockIdent (CondElse pos expr stmtTrue stmtFalse) = do
    tp <- eval expr
    if matchType tp (Bool pos)
        then do 
            (_, retTrue) <- typeCheck expectedType blockIdent stmtTrue
            (_, retFalse) <- typeCheck expectedType blockIdent stmtFalse
            case retTrue of
                NoRet -> return (id, NoRet)
                (DoRet _) -> return (id, retFalse)
        else throwError $ "Wrong return type at: " ++ posToStr pos ++ "\nExpected: " ++ show expectedType ++ "\nActual: " ++ show tp
typeCheck expectedType blockIdent (While pos expr loopStmt) = do
    tpCond <- eval expr
    case tpCond of
        Bool _ -> typeCheck expectedType blockIdent loopStmt
        _ -> throwError $ "Wrong expression type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tpCond
typeCheck expectedType _ (For pos valType ident exprSet exprCond incrStmt loopStmt) = do
    iterLoc <- newloc
    iterLoc <- newloc
    modifyMem $ Data.Map.insert iterLoc valType
    tpSet <- eval exprSet
    if matchType tpSet valType 
        then do
            tpCond <- local (Data.Map.insert ident iterLoc) (eval exprCond)
            if matchType tpCond (Bool Nothing)
                then do
                    local (Data.Map.insert ident iterLoc) 
                        (typeCheck expectedType (Data.Map.insert ident iterLoc Data.Map.empty) incrStmt)
                    local (Data.Map.insert ident iterLoc) 
                        (typeCheck expectedType (Data.Map.insert ident iterLoc Data.Map.empty) loopStmt)
                else throwError $ "Wrong expression type at: " ++ posToStr pos ++ "\nExpected: Bool\nActual: " ++ show tpCond
        else throwError $ "Wrong expression type at: " ++ posToStr pos ++ "\nExpected: " ++ show valType ++ "\nActual: " ++ show tpSet
typeCheck expectedType _ (ForEach pos valType ident expr loopStmt) = do
    val <- eval expr
    case val of
        (Array _ tp) -> if matchType tp valType
            then do
                loc <- newloc
                modifyMem $ Data.Map.insert loc valType
                local (Data.Map.insert ident loc) 
                    (typeCheck expectedType (Data.Map.insert ident loc Data.Map.empty) loopStmt)
            else throwError $ "Created type does not match assignment at: " ++ posToStr pos ++ "\tExpected: " ++ show valType ++ "\nActual: " ++ show tp
        _ -> throwError $ "Foreach requires array to iterate through at: " ++ posToStr pos
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

addTopDefs :: [TopDef] -> [TopDef] -> TypeCheckerMonad (IO ())
addTopDefs [] topDefs2 = runTopDefs topDefs2
addTopDefs ((FnDef pos ret ident args _block):lst) topDefs2 = do
    env <- ask
    case Data.Map.lookup ident env of
        Just _ -> throwError $ "Multiple definitions of: " ++ show ident ++ "  at: " ++ posToStr pos
        Nothing -> do
            loc <- newloc
            modifyMem (Data.Map.insert loc (Fun pos ret (Prelude.map argToType args)))
            local (Data.Map.insert ident loc) (addTopDefs lst topDefs2)

addBuildIntFunctions :: [BuiltInFunction] -> Program -> TypeCheckerMonad (IO ())
addBuildIntFunctions [] (Program pos topDefs) = addTopDefs topDefs topDefs
addBuildIntFunctions ((ident, tp, appFun):functions) program = do
    throwError "unimplemented"
    -- env <- ask
    -- loc <- newloc
    -- modifyMem (Data.Map.insert loc tp)
    -- local (Data.Map.insert ident loc) (addBuildIntFunctions functions program)

typeCheckProgram :: Program -> TypeCheckerMonad (IO ())
typeCheckProgram = addBuildIntFunctions builtInFunctions