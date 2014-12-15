
module Data.Bool where

open import Logic.Base
open import Logic.Id

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA Bool Bool True False #-}

infixr 12 _and_
infixr 10 _or_

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

not : Bool -> Bool
not true  = false
not false = true

_or_ : Bool -> Bool -> Bool
true  or _ = true
false or x = x

_and_ : Bool -> Bool -> Bool
true  and x = x
false and _ = false

isTrue : Bool -> Set
isTrue true  = True
isTrue false = False

isFalse : Bool -> Set
isFalse b = isTrue (not b)

satisfies : {A : Set} -> (A -> Bool) -> A -> Set
satisfies p x = isTrue (p x)

andElimL : forall {a b} -> isTrue (a and b) -> isTrue a
andElimL {true} _ = _
andElimL {false} ()

andElimR : forall a {b} -> isTrue (a and b) -> isTrue b
andElimR true p = p
andElimR false ()