{-# LANGUAGE UnicodeSyntax #-}

import Test.Framework (defaultMain)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit

import Control.Concurrent.Await
import Control.Concurrent.Await.Process
import System.Exit (ExitCode(..))
import System.Posix.Process (ProcessStatus(..))

test_true = do
  ph ← runProcess $ exec "true" []
  ps ← await ph
  ps @=? Exited ExitSuccess
  return ()

test_false = do
  ph ← runProcess $ exec "false" []
  ps ← await ph
  ps @=? Exited (ExitFailure 1)
  return ()

test_nonexistent = do
  ph ← runProcess $ exec "/n/o/n/e/x/i/s/t/e/n/t/" []
  ps ← await ph
  ps @=? Exited (ExitFailure 127)
  return ()

main = defaultMain
  [ testCase "true" test_true
  , testCase "false" test_false
  , testCase "nonexistent" test_nonexistent
  ]

