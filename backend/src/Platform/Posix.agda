-- Implementation of platform-specific functions
-- for Unix-like systems.
module Platform.Posix where

{-# FOREIGN AGDA2HS {-# LANGUAGE ScopedTypeVariables #-} #-}

{-# FOREIGN AGDA2HS

import Control.Concurrent
import Control.Exception (try, IOException)
import System.Posix.Signals
import System.Posix.Semaphore
import System.Posix.Files (stdFileMode)
import Foreign.C.Types (CInt)

-- It will be CInt so that it can be easily got as a parameter.
type SemName = CInt

-- Opens a new thread which is going to write its result into an MVar.
-- Also opens a "watcher thread"
-- which is going to wait on a POSIX named semaphore
-- with a name generated from the SemName parameter
-- and if it is unlocked, stops the calculation
-- and writes a Nothing into the MVar.
-- If the calculation runs successfully (so with Just sth),
-- the watcher thread is stopped by unlocking the semaphore;
-- if there is already a result in the MVar,
-- it does nothing.
-- The semaphore is created and removed by the watcher thread itself;
-- the "outer world" only needs to open it.
-- We also set a signal handler for SIGINT
-- which unlocks the semaphore.
runInterruptibly :: SemName -> IO a -> IO a -> IO a
runInterruptibly tid action resultOnInterrupt = do
  (mVar :: MVar (Maybe a)) <- newEmptyMVar
  childThreadId <- forkIO (putMVar mVar =<< (Just <$> action))

  let semaphoreName = show tid

  -- We create the semaphore here so that
  -- we can be sure it exists
  -- and can be accessed by both threads
  -- (otherwise, the thread creating it could be slower
  -- then the other one trying to access it).
  -- But it will be removed by the watcher thread
  -- as it will use it at last.
  semaphore <- semOpen semaphoreName
                       (OpenSemFlags True False)
                       stdFileMode
                       0

  watcherThreadId <- forkIO $ do
    -- an auto-reset event
    semaphore <- semOpen semaphoreName
                         (OpenSemFlags False False)
                         -- these are ignored
                         0 0
    -- this only blocks the current thread;
    -- semWait would block the entire runtime
    semThreadWait semaphore
    -- this will do nothing if the MVar has already been filled
    wasEmpty <- tryPutMVar mVar Nothing
    if wasEmpty
      then killThread childThreadId >> semUnlink semaphoreName
      else semUnlink semaphoreName

  oldHandler <- installHandler
    sigINT
    -- it should not fail if the semaphore does not exist anymore
    (CatchOnce $
       ((try :: IO () -> IO (Either IOException ())) $ semOpen semaphoreName (OpenSemFlags False False) 0 0 >>= semPost) >> return ())
    Nothing

  maybeResult <- readMVar mVar
  -- we reinstall the old Handler
  installHandler sigINT oldHandler Nothing
  case maybeResult of
    Just result -> do
      -- we make the watcher thread end gracefully
      -- by unlocking the semaphore
      semPost semaphore
      return result
    -- in this case, the watcher thread has already run
    -- and stopped the calculation thread
    Nothing -> resultOnInterrupt

#-}
