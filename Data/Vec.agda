
module Data.Vec where

open import Data.Bool
open import Data.Function
open import Data.Nat
open import Data.List
open import Data.Fin

infixr 30 _::_
data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat}(x : A)(xs : Vec A n) -> Vec A (suc n)

replicate : {n : Nat}{A : Set} -> A -> Vec A n
replicate {zero}  x = []
replicate {suc n} x = x :: replicate x

listToVec : forall {A}(xs : List A) -> Vec A (length xs)
listToVec [] = []
listToVec (x :: xs) = x :: listToVec xs

vecToList : forall {A n}(xs : Vec A n) -> List A
vecToList [] = []
vecToList (x :: xs) = x :: vecToList xs

padListToVec : {n : Nat}{A : Set}(x : A)(xs : List A){p : isTrue (length xs ≤ n)} -> Vec A n
padListToVec         z [] = replicate z
padListToVec {zero}  z (x :: xs) {}
padListToVec {suc n} z (x :: xs) {p} = x :: padListToVec z xs {p}

infixl 30 _!_
_!_ : {A : Set}{n : Nat} -> Vec A n -> Fin n -> A
[]      ! ()
x :: xs ! fzero =  x
x :: xs ! fsuc i = xs ! i

tabulate : {A : Set}{n : Nat} -> (Fin n -> A) -> Vec A n
tabulate {n = zero } f = []
tabulate {n = suc n} f = f fzero :: tabulate (f ∘ fsuc)

