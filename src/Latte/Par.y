-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.4.1).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Latte.Par
  ( happyError
  , myLexer
  , pProgram
  , pTopDef
  , pListTopDef
  , pArg
  , pListArg
  , pListClassElem
  , pClassElem
  , pBlock
  , pListStmt
  , pStmt
  , pItem
  , pListItem
  , pVar
  , pType
  , pListType
  , pNew
  , pExpr6
  , pExpr5
  , pExpr4
  , pExpr3
  , pExpr2
  , pExpr1
  , pExpr
  , pListExpr
  , pAddOp
  , pMulOp
  , pRelOp
  ) where

import Prelude

import qualified Latte.Abs
import Latte.Lex

}

%name pProgram_internal Program
%name pTopDef_internal TopDef
%name pListTopDef_internal ListTopDef
%name pArg_internal Arg
%name pListArg_internal ListArg
%name pListClassElem_internal ListClassElem
%name pClassElem_internal ClassElem
%name pBlock_internal Block
%name pListStmt_internal ListStmt
%name pStmt_internal Stmt
%name pItem_internal Item
%name pListItem_internal ListItem
%name pVar_internal Var
%name pType_internal Type
%name pListType_internal ListType
%name pNew_internal New
%name pExpr6_internal Expr6
%name pExpr5_internal Expr5
%name pExpr4_internal Expr4
%name pExpr3_internal Expr3
%name pExpr2_internal Expr2
%name pExpr1_internal Expr1
%name pExpr_internal Expr
%name pListExpr_internal ListExpr
%name pAddOp_internal AddOp
%name pMulOp_internal MulOp
%name pRelOp_internal RelOp
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '!'       { PT _ (TS _ 1)  }
  '!='      { PT _ (TS _ 2)  }
  '%'       { PT _ (TS _ 3)  }
  '&&'      { PT _ (TS _ 4)  }
  '('       { PT _ (TS _ 5)  }
  ')'       { PT _ (TS _ 6)  }
  '*'       { PT _ (TS _ 7)  }
  '+'       { PT _ (TS _ 8)  }
  '++'      { PT _ (TS _ 9)  }
  ','       { PT _ (TS _ 10) }
  '-'       { PT _ (TS _ 11) }
  '--'      { PT _ (TS _ 12) }
  '.'       { PT _ (TS _ 13) }
  '/'       { PT _ (TS _ 14) }
  ';'       { PT _ (TS _ 15) }
  '<'       { PT _ (TS _ 16) }
  '<='      { PT _ (TS _ 17) }
  '='       { PT _ (TS _ 18) }
  '=='      { PT _ (TS _ 19) }
  '>'       { PT _ (TS _ 20) }
  '>='      { PT _ (TS _ 21) }
  '['       { PT _ (TS _ 22) }
  '[]'      { PT _ (TS _ 23) }
  ']'       { PT _ (TS _ 24) }
  'boolean' { PT _ (TS _ 25) }
  'class'   { PT _ (TS _ 26) }
  'else'    { PT _ (TS _ 27) }
  'extends' { PT _ (TS _ 28) }
  'false'   { PT _ (TS _ 29) }
  'if'      { PT _ (TS _ 30) }
  'int'     { PT _ (TS _ 31) }
  'new'     { PT _ (TS _ 32) }
  'return'  { PT _ (TS _ 33) }
  'string'  { PT _ (TS _ 34) }
  'true'    { PT _ (TS _ 35) }
  'void'    { PT _ (TS _ 36) }
  'while'   { PT _ (TS _ 37) }
  '{'       { PT _ (TS _ 38) }
  '||'      { PT _ (TS _ 39) }
  '}'       { PT _ (TS _ 40) }
  L_Ident   { PT _ (TV _)    }
  L_integ   { PT _ (TI _)    }
  L_quoted  { PT _ (TL _)    }

%%

Ident :: { (Latte.Abs.BNFC'Position, Latte.Abs.Ident) }
Ident  : L_Ident { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Ident (tokenText $1)) }

Integer :: { (Latte.Abs.BNFC'Position, Integer) }
Integer  : L_integ  { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), (read (tokenText $1)) :: Integer) }

String  :: { (Latte.Abs.BNFC'Position, String) }
String   : L_quoted { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), ((\(PT _ (TL s)) -> s) $1)) }

Program :: { (Latte.Abs.BNFC'Position, Latte.Abs.Program) }
Program
  : ListTopDef { (fst $1, Latte.Abs.Program (fst $1) (snd $1)) }

TopDef :: { (Latte.Abs.BNFC'Position, Latte.Abs.TopDef) }
TopDef
  : Type Ident '(' ListArg ')' Block { (fst $1, Latte.Abs.FnDef (fst $1) (snd $1) (snd $2) (snd $4) (snd $6)) }
  | 'class' Ident '{' ListClassElem '}' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ClassDef (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4)) }
  | 'class' Ident 'extends' Ident '{' ListClassElem '}' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ClassExt (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4) (snd $6)) }

ListTopDef :: { (Latte.Abs.BNFC'Position, [Latte.Abs.TopDef]) }
ListTopDef
  : TopDef { (fst $1, (:[]) (snd $1)) }
  | TopDef ListTopDef { (fst $1, (:) (snd $1) (snd $2)) }

Arg :: { (Latte.Abs.BNFC'Position, Latte.Abs.Arg) }
Arg
  : Type Ident { (fst $1, Latte.Abs.Arg (fst $1) (snd $1) (snd $2)) }

ListArg :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Arg]) }
ListArg
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Arg { (fst $1, (:[]) (snd $1)) }
  | Arg ',' ListArg { (fst $1, (:) (snd $1) (snd $3)) }

ListClassElem :: { (Latte.Abs.BNFC'Position, [Latte.Abs.ClassElem]) }
ListClassElem
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | ClassElem ListClassElem { (fst $1, (:) (snd $1) (snd $2)) }

ClassElem :: { (Latte.Abs.BNFC'Position, Latte.Abs.ClassElem) }
ClassElem
  : Type Ident ';' { (fst $1, Latte.Abs.Attribute (fst $1) (snd $1) (snd $2)) }
  | Type Ident '(' ListArg ')' Block { (fst $1, Latte.Abs.Method (fst $1) (snd $1) (snd $2) (snd $4) (snd $6)) }

Block :: { (Latte.Abs.BNFC'Position, Latte.Abs.Block) }
Block
  : '{' ListStmt '}' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Block (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }

ListStmt :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Stmt]) }
ListStmt
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Stmt ListStmt { (fst $1, (:) (snd $1) (snd $2)) }

Stmt :: { (Latte.Abs.BNFC'Position, Latte.Abs.Stmt) }
Stmt
  : ';' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Empty (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | Block { (fst $1, Latte.Abs.BStmt (fst $1) (snd $1)) }
  | Type ListItem ';' { (fst $1, Latte.Abs.Decl (fst $1) (snd $1) (snd $2)) }
  | Ident '=' Expr ';' { (fst $1, Latte.Abs.Ass (fst $1) (snd $1) (snd $3)) }
  | Ident '++' ';' { (fst $1, Latte.Abs.Incr (fst $1) (snd $1)) }
  | Ident '--' ';' { (fst $1, Latte.Abs.Decr (fst $1) (snd $1)) }
  | 'return' Expr ';' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Ret (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | 'return' ';' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.VRet (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'if' '(' Expr ')' Stmt { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Cond (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | 'if' '(' Expr ')' Stmt 'else' Stmt { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.CondElse (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5) (snd $7)) }
  | 'while' '(' Expr ')' Stmt { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.While (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | Expr ';' { (fst $1, Latte.Abs.SExp (fst $1) (snd $1)) }

Item :: { (Latte.Abs.BNFC'Position, Latte.Abs.Item) }
Item
  : Ident { (fst $1, Latte.Abs.NoInit (fst $1) (snd $1)) }
  | Ident '=' Expr { (fst $1, Latte.Abs.Init (fst $1) (snd $1) (snd $3)) }

ListItem :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Item]) }
ListItem
  : Item { (fst $1, (:[]) (snd $1)) }
  | Item ',' ListItem { (fst $1, (:) (snd $1) (snd $3)) }

Var :: { (Latte.Abs.BNFC'Position, Latte.Abs.Var) }
Var
  : Ident { (fst $1, Latte.Abs.IdentVar (fst $1) (snd $1)) }
  | Var '[' Expr ']' { (fst $1, Latte.Abs.ArrayVar (fst $1) (snd $1) (snd $3)) }
  | Var '.' Ident { (fst $1, Latte.Abs.AttrVar (fst $1) (snd $1) (snd $3)) }

Type :: { (Latte.Abs.BNFC'Position, Latte.Abs.Type) }
Type
  : Ident { (fst $1, Latte.Abs.Class (fst $1) (snd $1)) }
  | Type '[]' { (fst $1, Latte.Abs.Array (fst $1) (snd $1)) }
  | 'int' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Int (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'string' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Str (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'boolean' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Bool (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'void' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Void (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }

ListType :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Type]) }
ListType
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Type { (fst $1, (:[]) (snd $1)) }
  | Type ',' ListType { (fst $1, (:) (snd $1) (snd $3)) }

New :: { (Latte.Abs.BNFC'Position, Latte.Abs.New) }
New
  : 'new' Type { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.NewBase (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | New '[' Expr ']' { (fst $1, Latte.Abs.NewArray (fst $1) (snd $1) (snd $3)) }

Expr6 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr6
  : New { (fst $1, Latte.Abs.ENew (fst $1) (snd $1)) }
  | Var { (fst $1, Latte.Abs.EVar (fst $1) (snd $1)) }
  | Integer { (fst $1, Latte.Abs.ELitInt (fst $1) (snd $1)) }
  | 'true' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ELitTrue (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | 'false' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.ELitFalse (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | Var '(' ListExpr ')' { (fst $1, Latte.Abs.EApp (fst $1) (snd $1) (snd $3)) }
  | String { (fst $1, Latte.Abs.EString (fst $1) (snd $1)) }
  | '(' Expr ')' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), (snd $2)) }

Expr5 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr5
  : '-' Expr6 { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Neg (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | '!' Expr6 { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Not (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | Expr6 { (fst $1, (snd $1)) }

Expr4 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr4
  : Expr4 MulOp Expr5 { (fst $1, Latte.Abs.EMul (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr5 { (fst $1, (snd $1)) }

Expr3 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr3
  : Expr3 AddOp Expr4 { (fst $1, Latte.Abs.EAdd (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr4 { (fst $1, (snd $1)) }

Expr2 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr2
  : Expr2 RelOp Expr3 { (fst $1, Latte.Abs.ERel (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr3 { (fst $1, (snd $1)) }

Expr1 :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr1
  : Expr2 '&&' Expr1 { (fst $1, Latte.Abs.EAnd (fst $1) (snd $1) (snd $3)) }
  | Expr2 { (fst $1, (snd $1)) }

Expr :: { (Latte.Abs.BNFC'Position, Latte.Abs.Expr) }
Expr
  : Expr1 '||' Expr { (fst $1, Latte.Abs.EOr (fst $1) (snd $1) (snd $3)) }
  | Expr1 { (fst $1, (snd $1)) }

ListExpr :: { (Latte.Abs.BNFC'Position, [Latte.Abs.Expr]) }
ListExpr
  : {- empty -} { (Latte.Abs.BNFC'NoPosition, []) }
  | Expr { (fst $1, (:[]) (snd $1)) }
  | Expr ',' ListExpr { (fst $1, (:) (snd $1) (snd $3)) }

AddOp :: { (Latte.Abs.BNFC'Position, Latte.Abs.AddOp) }
AddOp
  : '+' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Plus (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '-' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Minus (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }

MulOp :: { (Latte.Abs.BNFC'Position, Latte.Abs.MulOp) }
MulOp
  : '*' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Times (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '/' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Div (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '%' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.Mod (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }

RelOp :: { (Latte.Abs.BNFC'Position, Latte.Abs.RelOp) }
RelOp
  : '<' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.LTH (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '<=' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.LE (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '>' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.GTH (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '>=' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.GE (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '==' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.EQU (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }
  | '!=' { (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1), Latte.Abs.NE (uncurry Latte.Abs.BNFC'Position (tokenLineCol $1))) }

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

pTopDef :: [Token] -> Err Latte.Abs.TopDef
pTopDef = fmap snd . pTopDef_internal

pListTopDef :: [Token] -> Err [Latte.Abs.TopDef]
pListTopDef = fmap snd . pListTopDef_internal

pArg :: [Token] -> Err Latte.Abs.Arg
pArg = fmap snd . pArg_internal

pListArg :: [Token] -> Err [Latte.Abs.Arg]
pListArg = fmap snd . pListArg_internal

pListClassElem :: [Token] -> Err [Latte.Abs.ClassElem]
pListClassElem = fmap snd . pListClassElem_internal

pClassElem :: [Token] -> Err Latte.Abs.ClassElem
pClassElem = fmap snd . pClassElem_internal

pBlock :: [Token] -> Err Latte.Abs.Block
pBlock = fmap snd . pBlock_internal

pListStmt :: [Token] -> Err [Latte.Abs.Stmt]
pListStmt = fmap snd . pListStmt_internal

pStmt :: [Token] -> Err Latte.Abs.Stmt
pStmt = fmap snd . pStmt_internal

pItem :: [Token] -> Err Latte.Abs.Item
pItem = fmap snd . pItem_internal

pListItem :: [Token] -> Err [Latte.Abs.Item]
pListItem = fmap snd . pListItem_internal

pVar :: [Token] -> Err Latte.Abs.Var
pVar = fmap snd . pVar_internal

pType :: [Token] -> Err Latte.Abs.Type
pType = fmap snd . pType_internal

pListType :: [Token] -> Err [Latte.Abs.Type]
pListType = fmap snd . pListType_internal

pNew :: [Token] -> Err Latte.Abs.New
pNew = fmap snd . pNew_internal

pExpr6 :: [Token] -> Err Latte.Abs.Expr
pExpr6 = fmap snd . pExpr6_internal

pExpr5 :: [Token] -> Err Latte.Abs.Expr
pExpr5 = fmap snd . pExpr5_internal

pExpr4 :: [Token] -> Err Latte.Abs.Expr
pExpr4 = fmap snd . pExpr4_internal

pExpr3 :: [Token] -> Err Latte.Abs.Expr
pExpr3 = fmap snd . pExpr3_internal

pExpr2 :: [Token] -> Err Latte.Abs.Expr
pExpr2 = fmap snd . pExpr2_internal

pExpr1 :: [Token] -> Err Latte.Abs.Expr
pExpr1 = fmap snd . pExpr1_internal

pExpr :: [Token] -> Err Latte.Abs.Expr
pExpr = fmap snd . pExpr_internal

pListExpr :: [Token] -> Err [Latte.Abs.Expr]
pListExpr = fmap snd . pListExpr_internal

pAddOp :: [Token] -> Err Latte.Abs.AddOp
pAddOp = fmap snd . pAddOp_internal

pMulOp :: [Token] -> Err Latte.Abs.MulOp
pMulOp = fmap snd . pMulOp_internal

pRelOp :: [Token] -> Err Latte.Abs.RelOp
pRelOp = fmap snd . pRelOp_internal
}

