
module Data.Integer where

open import Data.Nat

-- Haskell integers
postulate Integer : Set

{-# BUILTIN INTEGER Integer #-}
{-# COMPILED_TYPE Integer Integer #-}

primitive
  primIntegerAbs   : Integer -> Nat
  primNatToInteger : Nat -> Integer

intToNat = primIntegerAbs
natToInt = primNatToInteger
