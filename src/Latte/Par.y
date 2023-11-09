-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.4.1).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Latte.Par
  ( happyError
  , myLexer
  , pProgram
  , pStmt
  , pListStmt
  , pExp1
  , pExp2
  , pExp3
  , pExp4
  , pExp
  ) where

import Prelude

import qualified Latte.Abs
import Latte.Lex

}

%name pProgram_internal Program
%name pStmt_internal Stmt
%name pListStmt_internal ListStmt
%name pExp1_internal Exp1
%name pExp2_internal Exp2
%name pExp3_internal Exp3
%name pExp4_internal Exp4
%name pExp_internal Exp
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '('      { PT _ (TS _ 1) }
  ')'      { PT _ (TS _ 2) }
  '*'      { PT _ (TS _ 3) }
  '+'      { PT _ (TS _ 4) }
  '-'      { PT _ (TS _ 5) }
  '/'      { PT _ (TS _ 6) }
  ';'      { PT _ (TS _ 7) }
  '='      { PT _ (TS _ 8) }
  L_Ident  { PT _ (TV _)   }
  L_integ  { PT _ (TI _)   }

%%

Ident :: { (Latte.Abs.BNFC'Position, Latte.Abs.Ident) }
Ident  : L_Ident { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Ident (tokenText $1)) }

Integer :: { (Latte.Abs.BNFC'Position, Integer) }
Integer  : L_integ  { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), (read (tokenText $1)) :: Integer) }

Program :: { (Latte.Abs.BNFC'Position, Latte.Abs.Program) }
Program : ListStmt { (fst $1, Latte.Abs.Prog (fst $1) (snd $1)) }

Stmt :: { (Latte.Abs.BNFC'Position, Latte.Abs.Stmt) }
Stmt
  : Ident '=' Exp { (fst $1, Latte.Abs.SAss (fst $1) (snd $1) (snd $3)) }
  | Exp { (fst $1, Latte.Abs.SExp (fst $1) (snd $1)) }

ListStmt :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Stmt]) }
ListStmt
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Stmt { (fst $1, (:[]) (snd $1)) }
  | Stmt ';' ListStmt { (fst $1, (:) (snd $1) (snd $3)) }

Exp1 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Exp) }
Exp1
  : Exp2 '+' Exp1 { (fst $1, Latte.Abs.ExpAdd (fst $1) (snd $1) (snd $3)) }
  | Exp2 { (fst $1, (snd $1)) }

Exp2 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Exp) }
Exp2
  : Exp2 '-' Exp3 { (fst $1, Latte.Abs.ExpSub (fst $1) (snd $1) (snd $3)) }
  | Exp3 { (fst $1, (snd $1)) }

Exp3 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Exp) }
Exp3
  : Exp3 '*' Exp4 { (fst $1, Latte.Abs.ExpMul (fst $1) (snd $1) (snd $3)) }
  | Exp3 '/' Exp4 { (fst $1, Latte.Abs.ExpDiv (fst $1) (snd $1) (snd $3)) }
  | Exp4 { (fst $1, (snd $1)) }

Exp4 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Exp) }
Exp4
  : Integer { (fst $1, Latte.Abs.ExpLit (fst $1) (snd $1)) }
  | Ident { (fst $1, Latte.Abs.ExpVar (fst $1) (snd $1)) }
  | '(' Exp ')' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), (snd $2)) }

Exp :: { (Latte.Abs.BNFC'Position, Latte.Abs.Exp) }
Exp : Exp1 { (fst $1, (snd $1)) }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err Latte.Abs.Program
pProgram = fmap snd . pProgram_internal

pStmt :: [Token] -> Err Latte.Abs.Stmt
pStmt = fmap snd . pStmt_internal

pListStmt :: [Token] -> Err [Latte.Abs.Stmt]
pListStmt = fmap snd . pListStmt_internal

pExp1 :: [Token] -> Err Latte.Abs.Exp
pExp1 = fmap snd . pExp1_internal

pExp2 :: [Token] -> Err Latte.Abs.Exp
pExp2 = fmap snd . pExp2_internal

pExp3 :: [Token] -> Err Latte.Abs.Exp
pExp3 = fmap snd . pExp3_internal

pExp4 :: [Token] -> Err Latte.Abs.Exp
pExp4 = fmap snd . pExp4_internal

pExp :: [Token] -> Err Latte.Abs.Exp
pExp = fmap snd . pExp_internal
}

