-- A data type which will contain
-- the variables of the application
-- in a mutable form.
-- A pointer to it will be passed to C++.
{-# OPTIONS --erasure --guardedness #-}

module AppState where

open import Haskell.Prelude
open import Haskell.Data.IORef


-- This has to be mutable,
-- because the C++ side will have a pointer
-- to the same instance
-- all the time.
-- That's why we cannot comfortably use
-- the State monad.

-- Here, add every variable you would like to persist
-- throughout the lifetime of your application,
-- within an IORef.
-- You can also add type variables,
-- like in this example.
record AppState (a : Set) : Set where
  constructor MkAppState
  field
    counterRef   : IORef a
open AppState public
{-# COMPILE AGDA2HS AppState #-}

-- An AppState initialised with a given number.
initAppState : {a : Set} {{num : Num a}} -> a -> IO (AppState a)
initAppState a = MkAppState <$> newIORef a
{-# COMPILE AGDA2HS initAppState #-}

