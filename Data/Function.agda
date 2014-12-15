
module Data.Function where

id : {A : Set} -> A -> A
id x = x

infixr 90 _∘_
_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (f : {x : A}(y : B x) -> C x y)(g : (x : A) -> B x)(x : A) -> C x (g x)
f ∘ g = \x -> f (g x)
