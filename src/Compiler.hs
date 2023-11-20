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

type LlvmMem = Int
type LlvmStore = (LlvmMem, Loc)

type VarVal = Integer

type InterpreterMonad = ExceptT String (ReaderT Env (StateT LlvmStore IO))

type Ret = (Env -> Env, VarVal)
    
newloc :: InterpreterMonad Loc
newloc = do
    (st,l) <- get
    put (st,l+1)
    return l

nextIdent :: InterpreterMonad String
nextIdent = do 
    (newIdent,l) <- get
    put (newIdent + 1,l)
    return $ "%" ++ show newIdent

getLoc :: BNFC'Position -> Ident -> InterpreterMonad Loc 
getLoc pos ident = do
    env <- ask
    case Data.Map.lookup ident env of
        Just loc -> return loc
        Nothing -> throwError ("undefined variable " ++ show ident ++ " at " ++ show pos)

getIdentLoc :: BNFC'Position -> Ident -> InterpreterMonad Loc
getIdentLoc pos ident = do
    getLoc pos ident

compileExpr :: Expr -> InterpreterMonad StringBuilder
compileExpr (ENew pos newVar) = throwError "unimplemented"
compileExpr (EVar pos var) = throwError "unimplemented"
compileExpr (ELitInt pos n) = throwError "unimplemented"
compileExpr (ELitTrue a) = throwError "unimplemented"
compileExpr (ELitFalse a) = throwError "unimplemented"
compileExpr (EApp pos var exprs) = throwError "unimplemented"
compileExpr (EString pos str) = throwError "unimplemented"
compileExpr (Neg pos expr) = throwError "unimplemented"
compileExpr (Not pos expr) = throwError "unimplemented"
compileExpr (EMul pos expr0 op expr1) = throwError "unimplemented"
compileExpr (EAdd pos expr0 op expr1) = throwError "unimplemented"
compileExpr (ERel pos expr0 op expr1) = throwError "unimplemented"
compileExpr (EAnd pos expr0 expr1) = throwError "unimplemented"
compileExpr (EOr pos expr0 expr1) = throwError "unimplemented"

compileStmt :: Stmt -> InterpreterMonad StringBuilder
compileStmt (Empty pos) = throwError "unimplemented"
compileStmt (BStmt pos block) = throwError "unimplemented"
compileStmt (Decl pos tp decls) = throwError "unimplemented"
compileStmt (Ass pos ident expr) = throwError "unimplemented"
compileStmt (Incr pos ident) = throwError "unimplemented"
compileStmt (Decr pos ident) = throwError "unimplemented"
compileStmt (Ret pos expr) = throwError "unimplemented"
compileStmt (VRet pos) = throwError "unimplemented"
compileStmt (Cond pos expr stmt) = throwError "unimplemented"
compileStmt (CondElse pos expr stmtTrue stmtFalse) = throwError "unimplemented"
compileStmt (While pos expr stmt) = throwError "unimplemented"
compileStmt (SExp pos expr) = throwError "unimplemented"


runTopDefs :: StringBuilder -> [TopDef] -> InterpreterMonad StringBuilder
runTopDefs code ((FnDef pos tp ident args block):lst) = throwError "unimplemented"
runTopDefs code ((ClassDef pos ident elems):lst) = throwError "unimplemented"
runTopDefs code ((ClassExt pos classIdent parentIdent elems):lst) = throwError "unimplemented"
runTopDefs code [] = do return code


compileProgram :: Program -> InterpreterMonad String
compileProgram (Program pos topDefs) = do
    code <- runTopDefs (BLst []) topDefs
    return $ buildString code