
module Data.Maybe where

import Control.Monad

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

{-# COMPILED_DATA Maybe Maybe Nothing Just #-}

withMaybe : {A B : Set} -> Maybe A -> B -> (A -> B) -> B
withMaybe nothing  z f = z
withMaybe (just x) z f = f x

bindMaybe : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
bindMaybe m f = withMaybe m nothing f

module MonadMaybe = Control.Monad just bindMaybe

mplus : {A : Set} -> Maybe A -> Maybe A -> Maybe A
mplus nothing  m = m
mplus (just x) _ = just x