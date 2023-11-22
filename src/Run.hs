module Run(runCompiler) where

import System.Process
import Compiler
import TypeChecker
import Data.Map
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.Either

import Latte.Abs

runCompiler :: Program -> String -> String -> IO ()
runCompiler program filePath fileName = do
    case evalState (runReaderT (runExceptT $ typeCheckProgram program) Data.Map.empty) (Data.Map.empty, 0) of
        Left mess -> putStrLn $ "type checker failed:\n\t" ++ mess
        Right _ -> do
            res <- evalStateT (runReaderT (runExceptT $ compileProgram program) Data.Map.empty) (1, 0)
            case res of
                Left mess -> putStrLn $ "compiler failed:\n\t" ++ mess
                Right llvmCode -> do
                    writeFile (filePath ++ "/" ++ fileName ++ ".ll") llvmCode
                    callCommand $ "llvm-as -o " ++ filePath ++ "/" ++ fileName ++ ".bc " ++ filePath ++ "/" ++ fileName ++ ".ll"