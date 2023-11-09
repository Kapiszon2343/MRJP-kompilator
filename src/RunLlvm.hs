module RunLlvm(runLlvm) where

import System.Process
import Llvm
import Data.Map
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.Either

import Instant.Abs

runLlvm :: Program -> String -> String -> IO ()
runLlvm program filePath fileName = do
    res <- evalStateT (runReaderT (runExceptT $ compileProgramLlvm program) Data.Map.empty) (1, 0)
    case res of
        Left mess -> putStrLn $ "compiler failed:\n\t" ++ mess
        Right llvmCode -> do
            writeFile (filePath ++ "/" ++ fileName ++ ".ll") llvmCode
            callCommand $ "llvm-as -o " ++ filePath ++ "/" ++ fileName ++ ".bc " ++ filePath ++ "/" ++ fileName ++ ".ll"