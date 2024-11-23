-- A file which contains
-- most of the interface of the application
-- to the C++ side.
{-# OPTIONS --erasure --guardedness #-}

module Interaction where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ForeignFunctionInterface, ScopedTypeVariables #-}

#-}

{-# FOREIGN AGDA2HS
import Foreign.C.Types

-- In order to be able to use threadDelay and unsafeCoerce:
import Control.Concurrent
import Unsafe.Coerce
#-}

open import Haskell.Prelude

open import Haskell.Data.IORef
open import Haskell.Foreign.StablePtr
open import Haskell.Foreign.Ptr
open import Haskell.Foreign.C.Types

open import AppState
open import Logic
open import Tool.Foreign
open import Tool.Future

-- Initialises the application state, with 0 as counter value.
-- Required type constraints have to be provided here, too.
initApp : {a : Set} {{num : Num a}} -> IO (StablePtr (AppState a))
initApp = newStablePtr =<< (MkAppState <$> newIORef 0)
{-# COMPILE AGDA2HS initApp #-}

-- Now, concrete instantiations
-- which can be exported.
initAppInteger : IO (StablePtr (AppState Integer))
initAppInteger = initApp
{-# COMPILE AGDA2HS initAppInteger #-}
-- And for example:
-- initAppDouble :: IO (StablePtr (AppState Double))
-- ...

-- Returns the current counter value.
getCounterValue : {a : Set} {{num : Num a}} -> StablePtr (AppState a) -> IO a
getCounterValue ptr = readIORef =<< (counterRef <$> deRefStablePtr ptr)
{-# COMPILE AGDA2HS getCounterValue #-}
getCounterValueInteger : StablePtr (AppState Integer) -> IO CInt
getCounterValueInteger ptr = unsafeIntegerToCInt <$> getCounterValue ptr
{-# COMPILE AGDA2HS getCounterValueInteger #-}

-- A subcall of incrementInteger
-- that can be easily called from within Haskell
-- (e.g. when writing the Haskell command prompt);
-- expecting a plain AppState instead of a StablePtr
-- and a native Integer instead of a CInt.
incrementInteger' : AppState Integer -> Integer -> IO (Either String Integer)
incrementInteger' appState x = do
  inner <- readIORef (counterRef appState)
  let either = eitherAddInteger inner x
  case either of λ where
    (Left err) -> return either -- @ patterns are not supported by agda2hs
    (Right result) -> do
      writeIORef (counterRef appState) result
      return either
{-# COMPILE AGDA2HS incrementInteger' #-}

-- For returning an undefined value.
postulate
  unsafeCoerce : {a b : Set} -> a -> b

-- For integerToInt.
{-# FOREIGN AGDA2HS
integerToInt :: Integer -> Int
integerToInt = fromIntegral
#-}

-- Increases the value of the counter with the given number.
-- Returns -1 if the value with which to increment is odd (in which case, it leaves the counter value unchanged);
-- and 0 on success.
-- Business logic should be provided not here,
-- but in Agda functions.
-- For now, we only write this for integers.
incrementInteger : StablePtr (AppState Integer) -> CInt -> IO CInt
incrementInteger ptr x = do
  appState <- deRefStablePtr ptr
  either <- incrementInteger' appState (cIntToInteger x)
  return $ (case either of λ where
    (Left _) -> unsafeIntegerToCInt (-1)
    (Right _) -> unsafeIntegerToCInt 0)
{-# COMPILE AGDA2HS incrementInteger #-}

postulate threadDelay : Int -> IO ⊤

-- Increases the counter with 2 every second
-- for the duration given or until interrupted,
-- and returns the result.
{-# TERMINATING #-}
increaseContinuouslyInteger : AppState Integer -> Int -> IO Integer
increaseContinuouslyInteger appState duration =
  if 0 < duration then (do
                          threadDelay 1000000
                          incrementInteger' appState 2
                          print =<< readIORef (counterRef appState)
                          increaseContinuouslyInteger appState (duration - 1))
  else readIORef (counterRef appState)
{-# COMPILE AGDA2HS increaseContinuouslyInteger #-}

-- Calls increaseContinuouslyInteger
-- and returns a Future for the result.
increaseContinuouslyIntegerAsync : AppState Integer -> Int -> IO (Future (Either String Integer))
increaseContinuouslyIntegerAsync appState duration = runAsync (increaseContinuouslyInteger appState duration)
{-# COMPILE AGDA2HS increaseContinuouslyIntegerAsync #-}

-- Calls increaseContinuouslyInteger'
-- and writes a Future to a C pointer given.
-- As the C side can only handle CInts, we convert the result.
increaseContinuouslyIntegerAsyncC : StablePtr (AppState Integer) -> Int -> Ptr (StablePtr PrimMVar) -> IO ⊤
increaseContinuouslyIntegerAsyncC = stablePtrise3 $ runAsyncC2
                                      (λ appState duration → unsafeIntegerToCInt <$> increaseContinuouslyInteger appState duration)
{-# COMPILE AGDA2HS increaseContinuouslyIntegerAsyncC #-}

-- Destruction of the StablePtr from the C side
-- is done by the hs_free_stable_ptr function.

{-# FOREIGN AGDA2HS
-- And the export clauses.

foreign export ccall initAppInteger :: IO (StablePtr (AppState Integer))
foreign export ccall getCounterValueInteger :: StablePtr (AppState Integer) -> IO CInt
foreign export ccall incrementInteger :: StablePtr (AppState Integer) -> CInt -> IO CInt
foreign export ccall increaseContinuouslyIntegerAsyncC :: StablePtr (AppState Integer) -> Int -> Ptr (StablePtr PrimMVar) -> IO ()
#-}
