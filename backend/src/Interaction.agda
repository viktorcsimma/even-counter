-- A file which contains
-- most of the interface of the application
-- to the C++ side.
{-# OPTIONS --erasure #-}

module Interaction where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ForeignFunctionInterface, ScopedTypeVariables #-}

import Prelude hiding (Rational)

import qualified Data.Map as Map
import Data.IORef
import Foreign.C.String
import Foreign.C.Types
import Foreign.StablePtr
import Foreign.Ptr
import Numeric.Natural

-- for interruption handling
import Control.Concurrent (threadDelay, ThreadId, myThreadId, throwTo, forkIO, killThread)
import Control.Concurrent.MVar
import Control.Exception
import Control.DeepSeq

import Logic
import AppState
import Platform
#-}

{-# FOREIGN AGDA2HS

-- Initialises the application state, with 0 as counter value.
-- Required type constraints have to be provided here, too.
initApp :: Num a => IO (StablePtr (AppState a))
initApp = newStablePtr =<< (MkAppState <$> newIORef 0)

-- Now, concrete instantiations
-- which can be exported.
initAppInt :: IO (StablePtr (AppState Integer))
initAppInt = initApp
foreign export ccall initAppInt :: IO (StablePtr (AppState Integer))
-- And for example:
-- initAppDouble :: IO (StablePtr (AppState Double))
-- ...

-- Returns the current counter value.
getCounterValue :: Num a => StablePtr (AppState a) -> IO a
getCounterValue ptr = readIORef =<< (counterRef <$> deRefStablePtr ptr)
getCounterValueInt :: StablePtr (AppState Integer) -> IO CInt
getCounterValueInt ptr = fromIntegral <$> getCounterValue ptr
foreign export ccall getCounterValueInt :: StablePtr (AppState Integer) -> IO CInt

-- Increases the value of the counter with the given number.
-- Returns -1 if the value with which to increment is odd (in which case, it leaves the counter value unchanged);
-- and 0 on success.
-- Business logic should be provided not here,
-- but in Agda functions.
-- For now, we only write this for integers.
incrementWithInt :: StablePtr (AppState Integer) -> CInt -> IO CInt
incrementWithInt ptr x = do
  appState <- deRefStablePtr ptr
  fromIntegral <$> incrementWithInt' appState (fromIntegral x)
foreign export ccall incrementWithInt :: StablePtr (AppState Integer) -> CInt -> IO CInt

-- A subcall of incrementWithInt
-- that can be easily called from within Haskell
-- (e.g. when writing the Haskell command prompt);
-- expecting a plain AppState instead of a StablePtr
-- and a native Integer instead of a CInt.
incrementWithInt' :: AppState Integer -> Integer -> IO Int
incrementWithInt' appState x = do
  inner <- readIORef (counterRef appState)
  case eitherAddInt inner (fromIntegral x) of
    Left err -> return (-1)
    Right result -> do
      writeIORef (counterRef appState) result
      return 0

-- Increases the counter by 2 every second
-- for the given number of seconds
-- or until getting interrupted.
-- Returns -1 if interrupted and 0 otherwise.
-- This shows how interruptible calculations
-- can be implemented.
increaseContinuouslyInt :: StablePtr (AppState Integer) -> CInt -> IO CInt
increaseContinuouslyInt ptr duration = do
  appState <- deRefStablePtr ptr
  fromIntegral <$> increaseContinuouslyInt' appState (fromIntegral duration)
foreign export ccall increaseContinuouslyInt :: StablePtr (AppState Integer) -> CInt -> IO CInt
-- increaseContinuouslyDouble :: StablePtr (AppState Double) -> CInt -> IO CInt
-- ...

-- A subcall of increaseContinuously
-- that can be easily called from within Haskell
-- (e.g. when writing the Haskell command prompt).
increaseContinuouslyInt' ::  AppState Integer -> Int -> IO Integer
increaseContinuouslyInt' appState duration = runInterruptibly (go appState duration) (-1)
  where
  go :: AppState Integer -> Int -> IO Integer
  go appState duration
    | 0 < duration     = do {threadDelay 1000000; incrementWithInt' appState 2;
                             print =<< readIORef (counterRef appState); go appState (duration - 1)}
    | otherwise        = return 0

-- Frees the StablePtr pointing to the AppState instance.
-- Should be called before the application finishes.
destructAppInt :: StablePtr (AppState Integer) -> IO ()
destructAppInt = freeStablePtr
foreign export ccall destructAppInt :: StablePtr (AppState Integer) -> IO ()
-- destructAppDouble :: StablePtr (AppState Double) -> IO ()
-- ...

#-}
