module InfoDigger where
import Control.Monad.State (StateT, MonadState (..), State, evalState)
import Latte.Abs

type MaxAppArgs = Int
type Info = MaxAppArgs
type DigInfoMonad = State Info

blankInfo :: Info
blankInfo = 0

setMaxAppArgs :: MaxAppArgs -> DigInfoMonad ()
setMaxAppArgs maxAppArgsNew = do
    maxAppArgsOld <- get
    put (max maxAppArgsOld maxAppArgsNew)
    return ()

digEAppInfo :: MaxAppArgs -> [Expr] ->  DigInfoMonad ()
digEAppInfo n [] = setMaxAppArgs n
digEAppInfo n (expr:exprs) = do
    digExprInfo expr
    digEAppInfo (n+1) exprs


digExprInfo :: Expr -> DigInfoMonad ()
digExprInfo (ENew pos newVar) = return () -- TODO new
digExprInfo (EVar pos var) = return ()
digExprInfo (ELitInt pos n) = return ()
digExprInfo (ELitTrue pos) = return ()
digExprInfo (ELitFalse pos) = return ()
digExprInfo (ELitArr pos []) = return ()
digExprInfo (ELitArr pos (expr:elems)) = do
    digExprInfo expr
    digExprInfo (ELitArr pos elems)
digExprInfo (ELitNull pos classIdent) = return ()
digExprInfo (EApp pos var exprs) = do
    digEAppInfo 0 exprs
    return ()
digExprInfo (EString pos str) = return ()
digExprInfo (ENeg pos expr) = digExprInfo expr
digExprInfo (ENot pos expr) = digExprInfo expr
digExprInfo (EMul pos expr1 op expr2) = do
    digExprInfo expr1
    digExprInfo expr2
digExprInfo (EAdd pos expr1 op expr2) = do
    digExprInfo expr1
    digExprInfo expr2
digExprInfo (ERel pos expr1 op expr2) = do
    digExprInfo expr1
    digExprInfo expr2
digExprInfo (EAnd pos expr1 expr2) = do
    digExprInfo expr1
    digExprInfo expr2
digExprInfo (EOr pos expr1 expr2) = do
    digExprInfo expr1
    digExprInfo expr2

digStmtInfo :: Stmt -> DigInfoMonad ()
digStmtInfo (Empty pos) = return ()
digStmtInfo (BStmt pos (Block _bPos [])) = digStmtInfo (Empty pos)
digStmtInfo (BStmt pos (Block bPos (stmt:stmts))) = do
    digStmtInfo stmt
    digStmtInfo (BStmt pos (Block bPos stmts))
digStmtInfo (Decl pos tp []) = digStmtInfo (Empty pos)
digStmtInfo (Decl _pos tp (decl:decls)) = do
    case decl of
        NoInit pos ident -> digStmtInfo (Decl _pos tp decls)
        Init pos ident expr -> do
            digExprInfo expr
            digStmtInfo (Decl _pos tp decls)
digStmtInfo (Ass pos var expr) = digExprInfo expr
digStmtInfo (Ret pos expr) = digExprInfo expr
digStmtInfo (Cond pos expr stmt) = digStmtInfo stmt
digStmtInfo (CondElse pos expr stmtTrue stmtFalse) = do
    digExprInfo expr
    digStmtInfo stmtTrue
    digStmtInfo stmtFalse
digStmtInfo (While pos expr stmt) = do
    digExprInfo expr
    digStmtInfo stmt
digStmtInfo (For pos incrTp incrIdent incrSet cond incrStmt blockStmt) = do
    digExprInfo incrSet
    digExprInfo cond
    digStmtInfo incrStmt
    digStmtInfo blockStmt
digStmtInfo (ForEach pos elemTp elemIdent arrExpr blockStmt) = do
    digExprInfo arrExpr
    digStmtInfo blockStmt
digStmtInfo (SExp pos expr) = digExprInfo expr
digStmtInfo _ = return ()

digStmtInfo' :: Stmt -> DigInfoMonad Info
digStmtInfo' stmt = do
    digStmtInfo stmt
    get

digStmtInfoPub :: Stmt -> Info
digStmtInfoPub stmt = evalState (digStmtInfo' stmt) blankInfo