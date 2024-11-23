-- A main program for a simple interpreter.
-- This is needed to be written in Haskell;
-- otherwise, Cabal does not accept it.
module Main where

import Data.Char (isDigit)
import Data.IORef
import Data.List (isPrefixOf)
import Data.Text (unpack, strip, pack)
import System.IO
import Text.Read (readMaybe)

import AppState
import Interaction
import Tool.Future

-- Command keywords.
aDD_KEYWORD :: String
aDD_KEYWORD = "add"
iNCFOR_KEYWORD :: String
iNCFOR_KEYWORD = "incfor"
eXIT_KEYWORD :: String
eXIT_KEYWORD = "exit"

main :: IO ()
main = do
  putStrLn $ "Welcome.\nType \"" ++ aDD_KEYWORD ++ " x\" to add an even number x to the counter; \"" ++ iNCFOR_KEYWORD ++ " n\" to increment continuously for n seconds; or \"" ++ eXIT_KEYWORD ++ "\" to exit."
  appState <- (MkAppState <$> newIORef 0)
  prompt appState

-- the second parameter is the precision to apply
prompt :: AppState Integer -> IO ()
prompt appState = do
  counter <- readIORef $ counterRef appState
  putStr $ "counter: " ++ show counter ++ "> "
  hFlush stdout   -- so that it gets printed immediately
  command <- (unpack . strip . pack) <$> getLine
  if command == eXIT_KEYWORD
  then do {putStrLn "Bye."; return ()}  else if (aDD_KEYWORD ++ " ") `isPrefixOf` command
  then do
    let num = (unpack . strip . pack) $ drop (length aDD_KEYWORD + 1) command
    case (readMaybe num :: Maybe Integer) of
      Just parsedInput -> do
        eitherStringResult <- incrementInteger' appState parsedInput
        case eitherStringResult of
          Left err -> do
            putStrLn err
            prompt appState
          _ -> prompt appState
      Nothing -> do
        putStrLn "Invalid syntax for :add – have you written the number correctly?"
        prompt appState
  else if (iNCFOR_KEYWORD ++ " ") `isPrefixOf` command
  then do
    let num = (unpack . strip . pack) $ drop (length iNCFOR_KEYWORD + 1) command
    if all isDigit num
    then do
      either <- getFromFuture =<< increaseContinuouslyIntegerAsync appState (read num)
      case either of
        Left err -> do {putStrLn err; prompt appState}
        _ -> prompt appState
    else do
      putStrLn "Invalid syntax for :incfor – have you written the number correctly?"
      prompt appState
  else do
    putStrLn "Unknown command. Try again."
    prompt appState
