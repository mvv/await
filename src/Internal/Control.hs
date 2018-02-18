{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE BangPatterns #-}

module Internal.Control (
    modifyMVar',
    modifyMVar_',
    updateMVar',
    updateMVar_'
  ) where

import Control.Monad (void)
import Control.Concurrent.MVar
import Control.Exception

modifyMVar' ∷ MVar α → (α → IO (α, β)) → IO β
modifyMVar' mv f = mask $ \restore → do
  v ← takeMVar mv
  (v', r) ← (restore $ f v) `onException` putMVar mv v
  putMVar mv $! v'
  return r

modifyMVar_' ∷ MVar α → (α → IO α) → IO ()
modifyMVar_' mv f = mask $ \restore → do
  v  ← takeMVar mv
  v' ← (restore $ f v) `onException` putMVar mv v
  putMVar mv $! v'

updateMVar' ∷ MVar α → (α → α) → IO α
updateMVar' mv f = mask_ $ do
  v ← takeMVar mv
  let !v' = f v
  putMVar mv v'
  return v'

updateMVar_' ∷ MVar α → (α → α) → IO ()
updateMVar_' mv f = void $ updateMVar' mv f

