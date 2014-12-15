
module Data.String where

open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Function

postulate
  String : Set
  Char   : Set
{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR Char #-}

{-# COMPILED_TYPE String String #-}
{-# COMPILED_TYPE Char Char #-}

primitive
  primStringAppend   : String -> String -> String
  primStringToList   : String -> List Char
  primStringFromList : List Char -> String
  primStringEquality : String -> String -> Bool

stringToList = primStringToList
listToString = primStringFromList

eqString = primStringEquality

infixr 40 _+++_
_+++_ = primStringAppend

strCat : List String -> String
strCat ss = foldr _+++_ "" ss

strLen : String -> Nat
strLen = length ∘ primStringToList