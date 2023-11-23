module Main where

import System.FilePath.Posix (takeBaseName, takeDirectory )
import Prelude
  ( ($), (.)
  , Either(..)
  , Int, (>)
  , String, (++), concat, unlines
  , Show, show
  , IO, (>>), (>>=), mapM_, putStrLn
  , FilePath
  , getContents, readFile
  )
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )
import Control.Monad.Reader ( runReaderT )
import Control.Monad.State ( evalState )
import Data.Map ( empty )

import Latte.Abs   ( Program )
import Latte.Lex   ( Token, mkPosToken )
import Latte.Par   ( pProgram, myLexer )
import Latte.Print ( Print, printTree )
import Latte.Skel  ()

import Run ( runCompiler )
import qualified Latte.Abs as Data.Map
import System.IO

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p (takeDirectory f) (takeBaseName f)

run :: Verbosity -> ParseFun Program -> String -> String -> String -> IO ()
run v p filePath fileName s =
  case p ts of
    Left err -> do
      hPutStrLn stderr "ERROR\n"
      hPutStrLn stderr err
      -- putStrLn "\nParse              Failed...\n"
      -- putStrV v "Tokens:"
      -- mapM_ (putStrV v . showPosToken . mkPosToken) ts
      -- putStrLn err
      exitFailure
    Right tree -> do
      -- putStrLn "\nParse Successful!"
      -- showTree v tree
      runCompiler tree filePath fileName
  where
  ts = myLexer s
  showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run 2 pProgram "." "Latte"
    "-s":fs    -> mapM_ (runFile 0 pProgram) fs
    fs         -> mapM_ (runFile 2 pProgram) fs

