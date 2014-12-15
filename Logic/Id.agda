
module Logic.Id where

infix 15 _==_
data _==_ {A : Set}(x : A) : {B : Set} -> B -> Set where
  refl : x == x

subst : {A : Set}(T : A -> Set){x y : A} -> x == y -> T y -> T x
subst T refl t = t

sym : {A : Set}{x y : A} -> x == y -> y == x
sym refl = refl

trans : {A : Set}{x y z : A} -> x == y -> y == z -> x == z
trans refl p = p

cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

cong₂ : forall {A B C}(f : A -> B -> C){a₁ a₂ b₁ b₂} -> a₁ == a₂ -> b₁ == b₂ -> f a₁ b₁ == f a₂ b₂
cong₂ f refl refl = refl

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl
