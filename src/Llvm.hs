module Llvm where

import Data.Map
import Data.Maybe (fromMaybe)
import Data.Bifunctor ( first )
import Control.Monad.State
import Control.Monad.Reader ( ReaderT (runReaderT), MonadReader(local, ask), asks )
import Control.Monad.Except

import Instant.Abs
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

eval :: Exp -> InterpreterMonad (StringBuilder, String)
eval (ExpLit _pos val) = do
    return (Str "", show val)
eval (ExpVar pos ident) = do
    loc <- getIdentLoc pos ident
    resIdent <- nextIdent
    return (Str $ "\t" ++ resIdent ++ " = load i32, i32* %" ++ identStr ident ++ "\n", resIdent)
eval (ExpMul _pos exp1 exp2) = do
    (code1, expIdent1) <- eval exp1
    (code2, expIdent2) <- eval exp2
    resIdent <- nextIdent
    return (Lst [
        code1,
        code2, 
        Str $ "\t" ++ resIdent ++ " = mul i32 " ++ expIdent1 ++ ", " ++ expIdent2 ++ "\n"], 
        resIdent)
eval (ExpDiv _pos exp1 exp2) = do
    (code1, expIdent1) <- eval exp1
    (code2, expIdent2) <- eval exp2
    resIdent <- nextIdent
    return (Lst [
        code1,
        code2, 
        Str $ "\t" ++ resIdent ++ " = sdiv i32 " ++ expIdent1 ++ ", " ++ expIdent2 ++ "\n"], 
        resIdent)
eval (ExpAdd _pos exp1 exp2) = do
    (code1, expIdent1) <- eval exp1
    (code2, expIdent2) <- eval exp2
    resIdent <- nextIdent
    return (Lst [
        code1, 
        code2, 
        Str $ "\t" ++ resIdent ++ " = add i32 " ++ expIdent1 ++ ", " ++ expIdent2 ++ "\n"], 
        resIdent)
eval (ExpSub _pos exp1 exp2) = do
    (code1, expIdent1) <- eval exp1
    (code2, expIdent2) <- eval exp2
    resIdent <- nextIdent
    return (Lst [
        code1,
        code2,
        Str $ "\t" ++ resIdent ++ " = sub i32 " ++ expIdent1 ++ ", " ++ expIdent2 ++ "\n"], 
        resIdent)

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


compileProgramLlvm :: Program -> InterpreterMonad String
compileProgramLlvm (Prog pos stmt) = do
    code <- runTopDefs (Lst [
        Str "declare i32 @printf(i8*, ...)\n\n",
        Str "@printInt = internal constant [4 x i8] c\"%d\\0A\\00\"\n\n",
        Str "define i32 @main(i32 %argc, i8** %argv) {\n"
        ]) stmt
    return $ buildString (Lst [code, Str "\tret i32 0\n}\n"]) 