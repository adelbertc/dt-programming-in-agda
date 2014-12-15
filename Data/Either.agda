
module Data.Either where

open import Control.Monad

data Either (A B : Set) : Set where
  inl : A -> Either A B
  inr : B -> Either A B

{-# COMPILED_DATA Either Either Left Right #-}

bindEither : {E A B : Set} -> Either E A -> (A -> Either E B) -> Either E B
bindEither (inl e) f = inl e
bindEither (inr x) f = f x

module MonadEither {E : Set} = Control.Monad {Either E} inr bindEither
