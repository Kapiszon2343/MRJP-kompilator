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
import System.IO (hPutStrLn, stderr)
import System.Exit

runCompiler :: Program -> String -> String -> IO ()
runCompiler program filePath fileName = do
    case typeCheckProgram program of
        Left mess -> do
            hPutStrLn stderr $ "ERROR\n" ++ mess
            exitFailure
        Right _ -> do
            hPutStrLn stderr "OK\n"
            exitSuccess
            res <- evalStateT (runReaderT (runExceptT $ compileProgram program) (Data.Map.empty, Data.Map.empty)) (1, 0)
            case res of
                Left mess -> do 
                    hPutStrLn stderr $ "ERROR\n" ++ mess
                    exitFailure
                Right llvmCode -> do
                    writeFile (filePath ++ "/" ++ fileName ++ ".ll") llvmCode
                    callCommand $ "llvm-as -o " ++ filePath ++ "/" ++ fileName ++ ".bc " ++ filePath ++ "/" ++ fileName ++ ".ll"