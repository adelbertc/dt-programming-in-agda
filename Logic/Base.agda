
module Logic.Base where

data   False : Set where
record True  : Set where

trivial : True
trivial = _ -- record{}
