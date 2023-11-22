-- File generated by the BNF Converter (bnfc 2.9.4.1).

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language Latte.

module Latte.Abs where

import Prelude (Integer, String)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String

type Program = Program' BNFC'Position
data Program' a = Program a [TopDef' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type TopDef = TopDef' BNFC'Position
data TopDef' a
    = FnDef a (Type' a) Ident [Arg' a] (Block' a)
    | ClassDef a Ident [ClassElem' a]
    | ClassExt a Ident Ident [ClassElem' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Arg = Arg' BNFC'Position
data Arg' a = Arg a (Type' a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type ClassElem = ClassElem' BNFC'Position
data ClassElem' a
    = Attribute a (Type' a) Ident
    | Method a (Type' a) Ident [Arg' a] (Block' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Block = Block' BNFC'Position
data Block' a = Block a [Stmt' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Stmt = Stmt' BNFC'Position
data Stmt' a
    = Empty a
    | BStmt a (Block' a)
    | Decl a (Type' a) [Item' a]
    | Ass a Ident (Expr' a)
    | Incr a Ident
    | Decr a Ident
    | Ret a (Expr' a)
    | VRet a
    | Cond a (Expr' a) (Stmt' a)
    | CondElse a (Expr' a) (Stmt' a) (Stmt' a)
    | While a (Expr' a) (Stmt' a)
    | For a (Type' a) Ident (Expr' a) (Expr' a) (Stmt' a) (Stmt' a)
    | ForEach a (Type' a) Ident (Expr' a) (Stmt' a)
    | SExp a (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Item = Item' BNFC'Position
data Item' a = NoInit a Ident | Init a Ident (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Var = Var' BNFC'Position
data Var' a
    = IdentVar a Ident
    | ArrayVar a (Var' a) (Expr' a)
    | AttrVar a (Var' a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Type = Type' BNFC'Position
data Type' a
    = Class a Ident
    | Array a (Type' a)
    | Int a
    | Str a
    | Bool a
    | Void a
    | Fun a (Type' a) [Type' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type New = New' BNFC'Position
data New' a = NewBase a (Type' a) | NewArray a (New' a) (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Expr = Expr' BNFC'Position
data Expr' a
    = ENew a (New' a)
    | EVar a (Var' a)
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | ELitArr a [Expr' a]
    | EApp a (Var' a) [Expr' a]
    | EString a String
    | Neg a (Expr' a)
    | Not a (Expr' a)
    | EMul a (Expr' a) (MulOp' a) (Expr' a)
    | EAdd a (Expr' a) (AddOp' a) (Expr' a)
    | ERel a (Expr' a) (RelOp' a) (Expr' a)
    | EAnd a (Expr' a) (Expr' a)
    | EOr a (Expr' a) (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type AddOp = AddOp' BNFC'Position
data AddOp' a = Plus a | Minus a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MulOp = MulOp' BNFC'Position
data MulOp' a = Times a | Div a | Mod a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type RelOp = RelOp' BNFC'Position
data RelOp' a = LTH a | LE a | GTH a | GE a | EQU a | NE a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    Program p _ -> p

instance HasPosition TopDef where
  hasPosition = \case
    FnDef p _ _ _ _ -> p
    ClassDef p _ _ -> p
    ClassExt p _ _ _ -> p

instance HasPosition Arg where
  hasPosition = \case
    Arg p _ _ -> p

instance HasPosition ClassElem where
  hasPosition = \case
    Attribute p _ _ -> p
    Method p _ _ _ _ -> p

instance HasPosition Block where
  hasPosition = \case
    Block p _ -> p

instance HasPosition Stmt where
  hasPosition = \case
    Empty p -> p
    BStmt p _ -> p
    Decl p _ _ -> p
    Ass p _ _ -> p
    Incr p _ -> p
    Decr p _ -> p
    Ret p _ -> p
    VRet p -> p
    Cond p _ _ -> p
    CondElse p _ _ _ -> p
    While p _ _ -> p
    For p _ _ _ _ _ _ -> p
    ForEach p _ _ _ _ -> p
    SExp p _ -> p

instance HasPosition Item where
  hasPosition = \case
    NoInit p _ -> p
    Init p _ _ -> p

instance HasPosition Var where
  hasPosition = \case
    IdentVar p _ -> p
    ArrayVar p _ _ -> p
    AttrVar p _ _ -> p

instance HasPosition Type where
  hasPosition = \case
    Class p _ -> p
    Array p _ -> p
    Int p -> p
    Str p -> p
    Bool p -> p
    Void p -> p
    Fun p _ _ -> p

instance HasPosition New where
  hasPosition = \case
    NewBase p _ -> p
    NewArray p _ _ -> p

instance HasPosition Expr where
  hasPosition = \case
    ENew p _ -> p
    EVar p _ -> p
    ELitInt p _ -> p
    ELitTrue p -> p
    ELitFalse p -> p
    ELitArr p _ -> p
    EApp p _ _ -> p
    EString p _ -> p
    Neg p _ -> p
    Not p _ -> p
    EMul p _ _ _ -> p
    EAdd p _ _ _ -> p
    ERel p _ _ _ -> p
    EAnd p _ _ -> p
    EOr p _ _ -> p

instance HasPosition AddOp where
  hasPosition = \case
    Plus p -> p
    Minus p -> p

instance HasPosition MulOp where
  hasPosition = \case
    Times p -> p
    Div p -> p
    Mod p -> p

instance HasPosition RelOp where
  hasPosition = \case
    LTH p -> p
    LE p -> p
    GTH p -> p
    GE p -> p
    EQU p -> p
    NE p -> p

