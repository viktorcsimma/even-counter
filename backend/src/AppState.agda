-- A data type which will contain
-- the variables of the application
-- in a mutable form.
-- A pointer to it will be passed to C++.
-- This is actually written in Haskell.
{-# OPTIONS --erasure --guardedness #-}

module AppState where

-- Add dependencies of the Haskell part here, too,
-- so that agda2hs knows this depends on them.
-- import My.Module

{-# FOREIGN AGDA2HS
import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.IORef

-- And here, too.
-- import My.Module
#-}

{-# FOREIGN AGDA2HS
-- And now the Haskell-specific, side-effect-ridden side.

-- This has to be mutable,
-- because the C++ side will have a pointer
-- to the same instance
-- all the time.
-- That's why I cannot comfortably use
-- the State monad.

-- Here, add every variable you would like to persist
-- throughout the lifetime of your application,
-- within an IORef.
-- You can also add type variables,
-- like in this example.
data AppState a = MkAppState
  { counterRef   :: IORef a
  }

-- An AppState initialised with 0.
zeroAppState :: Num a => IO (AppState a)
zeroAppState = MkAppState <$> newIORef 0
#-}
