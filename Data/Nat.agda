
module Data.Nat where

open import Data.Bool

infixl 60 _*_
infixl 40 _+_

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero  * m = zero
suc n * m = m + n * m

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

_≤_ : Nat -> Nat -> Bool
zero  ≤ m     = true
suc n ≤ zero  = false
suc n ≤ suc m = n ≤ m
