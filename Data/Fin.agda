
module Data.Fin where

open import Data.Nat

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat}(i : Fin n) -> Fin (suc n)
