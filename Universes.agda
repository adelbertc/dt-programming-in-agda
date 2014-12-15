module Universes where

data False : Set where
record True : Set where

data Bool : Set where
  true : Bool
  false : Bool

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

not_ : Bool -> Bool
not true = false
not false = true

_and_ : Bool -> Bool -> Bool
true and x = x
false and _ = false

noNotId : (a : Bool) -> isTrue (not not a) -> isTrue a
noNotId true p = p
noNotId false ()

andIntro : (a b : Bool) -> isTrue a -> isTrue b -> isTrue (a and b)
andIntro true _ _ p = p
andIntro false _ () _

open import Data.Nat

nonZero : Nat -> Bool
nonZero zero = false
nonZero (suc _) = true

postulate _div_ : Nat -> (m : Nat) {p : isTrue (nonZero m)} -> Nat

three = 16 div 5

data Functor : Set1 where
  |Id| : Functor
  |K| : Set -> Functor
  _|+|_ : Functor -> Functor -> Functor
  _|x|_ : Functor -> Functor -> Functor

data _⊕_ (A B : Set) : Set where
  inl : A -> A ⊕ B
  inr : B -> A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _×_

[_] : Functor -> Set -> Set
[ |Id| ] X = X
[ |K| A ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X × [ G ] X

map : (F : Functor) {X Y : Set} -> (X -> Y) -> [ F ] X -> [ F ] Y
map |Id| f x = f x
map (|K| A) f c = c
map (F |+| G) f (inl x) = inl (map F f x)
map (F |+| G) f (inr y) = inr (map G f y)
map (F |x| G) f (x , y) = map F f x , map G f y

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) -> μ F

mapFold : forall {X} F G -> ([ G ] X -> X) -> [ F ] (μ G) -> [ F ] X
mapFold |Id| G φ < x > = φ (mapFold G G φ x)
mapFold (|K| A) G φ c = c
mapFold (F1 |+| F2) G φ (inl x) = inl (mapFold F1 G φ x)
mapFold (F1 |+| F2) G φ (inr y) = inr (mapFold F2 G φ y)
mapFold (F1 |x| F2) G φ (x , y) = mapFold F1 G φ x , mapFold F2 G φ y

fold : {F : Functor} {A : Set} -> ([ F ] A -> A) -> μ F -> A
fold {F} φ < x > = φ (mapFold F F φ x)

NatF = |K| True |+| |Id|
NAT = μ NatF

Z : NAT
Z = < inl _ >

S : NAT -> NAT
S n = < inr n >

ListF = \A -> |K| True |+| |K| A |x| |Id|
LIST = \A -> μ (ListF A)

nil : {A : Set} -> LIST A
nil = < inl _ >

cons : {A : Set} -> A -> LIST A -> LIST A
cons x xs = < inr (x , xs) >

[_||_] : {A B C : Set} -> (A -> C) -> (B -> C) -> A ⊕ B -> C
[ f || g ] (inl x) = f x
[ f || g ] (inr y) = g y

uncurry : {A B C : Set} -> (A -> B -> C) -> A × B -> C
uncurry f (x , y) = f x y

const : {A B : Set} -> A -> B -> A
const x y = x

foldr : {A B : Set} -> (A -> B -> B) -> B -> LIST A -> B
foldr {A}{B} f z = fold [ const z || uncurry f ]

plus : NAT -> NAT -> NAT
plus n m = fold [ const m || S ] n

open import Data.List

data Type : Set where
  bool : Type
  nat : Type
  list : Type -> Type
  pair : Type -> Type -> Type

El : Type -> Set
El nat = Nat
El bool = Bool
El (list a) = List (El a)
El (pair a b) = El a × El b

infix 30 _==_
_==_ : {a : Type} -> El a -> El a -> Bool
_==_ {nat} zero zero = true
_==_ {nat} (suc _) zero = false
_==_ {nat} zero (suc _) = false
_==_ {nat} (suc n) (suc m) = n == m

_==_ {bool} true x = x
_==_ {bool} false x = not x

_==_ {list a} [] [] = true
_==_ {list a} (_ :: _) [] = false
_==_ {list a} [] (_ :: _) = true
_==_ {list a} (x :: xs) (y :: ys) = x == y and xs == ys

_==_ {pair a b} (x1 , y1) (x2 , y2) = x1 == x2 and y1 == y2

example1 : isTrue (2 + 2 == 4)
example1 = _

example2 : isTrue (not (true :: false :: [] == true :: true :: []))
example2 = _

-- Exercise 3.1

data Compare : Nat -> Nat -> Set where
  less : forall {n} k -> Compare n (n + suc k)
  more : forall {n} k -> Compare (n + suc k) n
  same : forall {n} -> Compare n n

-- a
compare : (n m : Nat) -> Compare n m
compare zero zero = same
compare zero (suc n) = less n
compare (suc n) zero = more n
compare (suc n) (suc m) with compare n m
compare (suc n) (suc .(n + suc k)) | less k = less k
compare (suc .(n + suc k)) (suc n) | more k = more k
compare (suc n) (suc .n) | same = same

-- b
difference : Nat -> Nat -> Nat
difference n m with compare n m
difference n .(n + suc k) | less k = zero
difference .(n + suc k) n | more k = suc k
difference n .n | same = zero

-- Exercise 3.2
-- a
data Type' : Set where
  l : Type'
  _=>_ : Type' -> Type' -> Type'

data _≠_ : Type' -> Type' -> Set where
 l-func : forall {σ τ} -> l ≠ (σ => τ)
 func-l : forall {σ τ} -> (σ => τ) ≠ l
 func-in : forall {σ1 σ2 τ} -> σ1 ≠ σ2 -> (σ1 => τ) ≠ (σ2 => τ)
 func-out : forall {σ τ1 τ2} -> τ1 ≠ τ2 -> (σ => τ1) ≠ (σ => τ2)
 func-func : forall {σ1 σ2 τ1 τ2} -> σ1 ≠ τ1 -> σ2 ≠ τ2 -> (σ1 => σ2) ≠ (τ1 => τ2)

data Equal? : Type' -> Type' -> Set where
  yes : forall {τ} -> Equal? τ τ
  no : forall {σ τ} -> σ ≠ τ -> Equal? σ τ

_=?=_ : (σ τ : Type') -> Equal? σ τ
l =?= l = yes
l =?= (_ => _) = no l-func
(_ => _) =?= l = no func-l
(σ1 => τ1) =?= (σ2 => τ2) with σ1 =?= σ2 | τ1 =?= τ2
(σ => τ) =?= (.σ => .τ) | yes | yes = yes
(σ => τ1) =?= (.σ => τ2) | yes | no p = no (func-out p)
(σ1 => τ) =?= (σ2 => .τ) | no p | yes = no (func-in p)
(σ1 => τ1) =?= (σ2 => τ2) | no p1 | no p2 = no (func-func p1 p2)

-- b
Cxt = List Type'

infixl 80 _$_
data Raw : Set where
  var : Nat -> Raw
  _$_ : Raw -> Raw -> Raw
  lam : Type' -> Raw -> Raw

data _∈_ {A : Set} (x : A) : List A -> Set where
  hd : forall {xs} -> x ∈ x :: xs
  tl : forall {y xs} -> x ∈ xs -> x ∈ y :: xs

data Term (Γ : Cxt) : Type' -> Set where
  var : forall {τ} -> τ ∈ Γ -> Term Γ τ
  _$_ : forall {σ τ} -> Term Γ (σ => τ) -> Term Γ σ -> Term Γ τ
  lam : forall σ {τ} -> Term (σ :: Γ) τ -> Term Γ (σ => τ)

index : forall {A} {x : A} {xs} -> x ∈ xs -> Nat
index hd = zero
index (tl p) = suc (index p)

erase : forall {γ τ} -> Term γ τ -> Raw
erase (var x) = var (index x)
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

data BadTerm (Γ : Cxt) : Set where
  var : {m n : Nat} -> length Γ + m ≡ n -> BadTerm Γ
  bt : BadTerm Γ -> Raw -> BadTerm Γ
  te : Term Γ l -> Raw -> BadTerm Γ
  btte : {σ τ : Type'} -> Term Γ (σ => τ) -> BadTerm Γ -> BadTerm Γ
  ne : {σ σ' τ : Type'} -> σ ≠ σ' -> Term Γ (σ => τ) -> Term Γ σ' -> BadTerm Γ
  lam : {σ : Type'} -> BadTerm (σ :: Γ) -> BadTerm Γ

eraseBad : {Γ : Cxt} -> BadTerm Γ -> Raw
eraseBad (var {_} {n} _) = var n
eraseBad (bt b r) = (eraseBad b) $ r
eraseBad (te t r) = (erase t) $ r
eraseBad (btte t b) = (erase t) $ (eraseBad b)
eraseBad (ne _ t1 t2) = (erase t1) $ (erase t2)
eraseBad (lam {σ} b) = lam σ (eraseBad b)

data Infer (Γ : Cxt) : Raw -> Set where
  ok : (τ : Type') (t : Term Γ τ) -> Infer Γ (erase t)
  bad : (b : BadTerm Γ) -> Infer Γ (eraseBad b)

data Lookup {A : Set} (xs : List A) : Nat -> Set where
  inside : (x : A) (p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : Nat) -> Lookup xs (length xs + m)

_!_ : {A : Set} (xs : List A) (n : Nat) -> Lookup xs n
[] ! n = outside n
(x :: xs) ! zero = inside x hd
(x :: xs) ! suc n with xs ! n
(x :: xs) ! suc .(index p) | inside y p = inside y (tl p)
(x :: xs) ! suc .(length xs + n) | outside n = outside n

infer : (Γ : Cxt) (e : Raw) -> Infer Γ e
infer Γ (var n) with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = bad (var refl)
infer Γ (var .(index x)) | inside σ x = ok σ (var x)
infer Γ (e1 $ e2) with infer Γ e1
infer Γ (.(eraseBad b1) $ e2) | bad b1 = bad (bt b1 e2)
infer Γ (.(erase t1) $ e2) | ok l t1 = bad (te t1 e2)
infer Γ (.(erase t1) $ e2) | ok (σ => τ) t1
  with infer Γ e2
infer Γ (.(erase t1) $ .(eraseBad b2)) | ok (σ => τ) t1 | bad b2 = bad (btte t1 b2)
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ => τ) t1 | ok σ' t2
  with σ =?= σ'
infer Γ (.(erase t1) $ .(erase t2))
  | ok (σ => τ) t1 | ok .σ t2 | yes = ok τ (t1 $ t2)
infer Γ (.(erase t1) $ .(erase t2))
  | ok (σ => τ) t1 | ok σ' t2 | no p = bad (ne p t1 t2)
infer Γ (lam σ e) with infer (σ :: Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ => τ) (lam σ t)
infer Γ (lam σ .(eraseBad b)) | bad b = bad (lam b)

-- Exercises 3.3
infixr 30 _::_
data All {A : Set} (P : A -> Set) : List A -> Set where
  [] : All P []
  _::_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)

-- a
lemma-All-∈ : forall {A x xs} {P : A -> Set} -> All P xs -> x ∈ xs -> P x
lemma-All-∈ [] ()
lemma-All-∈ (x :: xs) hd = x
lemma-All-∈ (x :: xs) (tl p) = lemma-All-∈ xs p

-- b
data Inspect {A : Set} (x : A) : Set where
  it : (y : A) -> x ≡ y -> Inspect x

inspect : {A : Set} (x : A) -> Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} -> x ≡ true -> isTrue x
trueIsTrue refl = _

satisfies' : {A : Set} -> (A -> Bool) -> A -> Set
satisfies' p x = isTrue (p x)

filter' : {A : Set} -> (A -> Bool) -> List A -> List A
filter' _ [] = []
filter' p (x :: xs) with p x
... | true = x :: filter' p xs
... | false = filter' p xs

lem-filter-sound : {A : Set} (p : A -> Bool) (xs : List A) -> All (satisfies' p) (filter' p xs)
lem-filter-sound p [] = []
lem-filter-sound p (x :: xs) with inspect (p x)
lem-filter-sound p (x :: xs) | it y eq with p x | eq
lem-filter-sound p (x :: xs) | it .true eq | true | refl = trueIsTrue eq :: lem-filter-sound p xs
lem-filter-sound p (x :: xs) | it .false eq | false | refl = lem-filter-sound p xs

lem-filter-complete : {A : Set} (p : A -> Bool) (x : A) {xs : List A} -> x ∈ xs -> satisfies' p x -> x ∈ filter' p xs
lem-filter-complete p x {[]} () px
lem-filter-complete p x {.x :: xs} hd t with (p x)
lem-filter-complete p x {.x :: xs} hd () | false
lem-filter-complete p x {.x :: xs} hd t | true = hd
lem-filter-complete p x {y :: ys} (tl ev) px with inspect (p y)
lem-filter-complete p x {y :: ys} (tl ev) px | it py proof with p y | proof
lem-filter-complete p x {y :: ys} (tl ev) px | it .true proof | true | refl = tl (lem-filter-complete p x {ys} ev px)
lem-filter-complete p x {y :: ys} (tl ev) px | it .false proof | false | refl = lem-filter-complete p x {ys} ev px

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

{-# COMPILED_DATA Maybe Maybe Nothing Just #-}

postulate IO : Set -> Set
{-# COMPILED_TYPE IO IO #-}

open import Data.String

postulate
  putStrLn : String -> IO Unit

{-# COMPILED putStrLn putStrLn #-}
