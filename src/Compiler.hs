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

eval :: Expr -> InterpreterMonad (StringBuilder, String)


runTopDefs :: StringBuilder -> [Stmt] -> InterpreterMonad StringBuilder
runTopDefs code ((SAss pos ident exp):lst) = do
    (valCode, expIdent) <- eval exp
    let currIdent = "%" ++ identStr ident
    env <- ask
    case Data.Map.lookup ident env of
        Just loc -> do
            runTopDefs (Lst [code, valCode, Str $ "\tstore i32 " ++ expIdent ++ ", i32* " ++ currIdent ++ "\n"]) lst
        Nothing -> do
            loc <- newloc
            local (Data.Map.insert ident loc) (runTopDefs (Lst [
                code,
                valCode, 
                Str $ "\t" ++ currIdent ++ " = alloca i32\n" ++
                "\tstore i32 " ++ expIdent ++ ", i32* " ++ currIdent ++ "\n"]) lst)
runTopDefs code ((SExp pos exp):lst) = do
    (resCode, expIdent) <- eval exp
    printStrIdent <- nextIdent
    callIdent <- nextIdent
    runTopDefs (Lst [
        code,
        resCode, 
        Str $ "\t" ++ printStrIdent ++ " = getelementptr [4 x i8], [4 x i8]* @printInt, i32 0, i32 0\n" ++
        "\t" ++ callIdent ++ " = call i32(i8*, ...) @printf(i8* " ++ printStrIdent ++ ", i32 " ++ expIdent ++ ")\n"])
        lst
runTopDefs code [] = do return code


compileProgram :: Program -> InterpreterMonad String
compileProgram (Prog pos stmt) = do
    code <- runTopDefs (Lst [
        Str "declare i32 @printf(i8*, ...)\n\n",
        Str "@printInt = internal constant [4 x i8] c\"%d\\0A\\00\"\n\n",
        Str "define i32 @main(i32 %argc, i8** %argv) {\n"
        ]) stmt
    return $ buildString (Lst [code, Str "\tret i32 0\n}\n"]) 