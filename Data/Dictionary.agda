
open import Data.Bool

module Data.Dictionary {Key : Set}(_==_ : Key -> Key -> Bool) where

open import Data.Pair
open import Data.List

Dict : Set -> Set
Dict A = List (Key × A)

hasKey : {A : Set} -> Key -> Dict A -> Bool
hasKey _ [] = false
hasKey y ((x , _) :: xs) = x == y or hasKey y xs

HasKey : {A : Set} -> Key -> Dict A -> Set
HasKey x xs = isTrue (hasKey x xs)

lookup : {A : Set}(x : Key)(xs : Dict A){p : HasKey x xs} -> A
lookup _ [] {}
lookup y ((x , v) :: xs) {p} with x == y
... | true  = v
... | false = lookup y xs {p}

hasKeys : {A : Set} -> List Key -> Dict A -> Bool
hasKeys []        _ = true
hasKeys (x :: xs) t = hasKey x t and hasKeys xs t

HasKeys : {A : Set} -> List Key -> Dict A -> Set
HasKeys xs t = isTrue (hasKeys xs t)

project : {A : Set}(xs : List Key)(tbl : Dict A){p : HasKeys xs tbl} ->
          Dict A
project []        tbl     = []
project (x :: xs) tbl {p} = (x , lookup x tbl {andElimL p}) ::
                            project xs tbl {andElimR (hasKey x tbl) p}

distinctKeys : {A : Set} -> Dict A -> Bool
distinctKeys []              = true
distinctKeys ((x , _) :: xs) = not (hasKey x xs) and distinctKeys xs 

disjoint : {A : Set} -> Dict A -> Dict A -> Bool
disjoint xs ys = distinctKeys (xs ++ ys)

Disjoint : {A : Set} -> Dict A -> Dict A -> Set
Disjoint xs ys = isTrue (disjoint xs ys)
