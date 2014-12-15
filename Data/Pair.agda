
module Data.Pair where

infixr 10 _×_ _,_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

fst : {A B : Set} -> A × B -> A
fst (x , y) = x

snd : {A B : Set} -> A × B -> B
snd (x , y) = y