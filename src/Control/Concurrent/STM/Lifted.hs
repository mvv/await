{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Concurrent.STM.Lifted (
    module Control.Monad.STM.Lifted,
    TVar,
    newTVar,
    newTVarIO,
    readTVar,
    readTVarIO,
    writeTVar,
    registerDelay 
  ) where

import Data.Maybe (fromJust)
import Data.Timeout
import Control.Monad (void)
import Control.Monad.Base
import Control.Monad.STM.Lifted
import Control.Concurrent.STM.TVar (TVar)
import qualified Control.Concurrent.STM.TVar as STM
import GHC.Event (registerTimeout)
#if MIN_VERSION_base(4,7,0)
import GHC.Event (getSystemTimerManager)
#else
import GHC.Event (getSystemEventManager)
#endif

newTVar ∷ MonadBase STM μ ⇒ α → μ (TVar α)
newTVar = liftBase . STM.newTVar

newTVarIO ∷ MonadBase IO μ ⇒ α → μ (TVar α) 
newTVarIO = liftBase . STM.newTVarIO

readTVar ∷ MonadBase STM μ ⇒ TVar α → μ α
readTVar = liftBase . STM.readTVar

readTVarIO ∷ MonadBase IO μ ⇒ TVar α → μ α
readTVarIO = liftBase . STM.readTVarIO

writeTVar ∷ MonadBase STM μ ⇒ TVar α → α → μ ()
writeTVar tv v = liftBase $ STM.writeTVar tv v

registerDelay ∷ MonadBase IO μ ⇒ Timeout → μ (TVar Bool)
registerDelay tt = liftBase $
  if tt == instantly
    then STM.newTVarIO True
    else do
      ttv ← STM.newTVarIO False
#if MIN_VERSION_base(4,7,0)
      tmm ← getSystemTimerManager
#else
      Just tmm ← getSystemEventManager
#endif
      let us = tt #> MicroSecond
          maxUs = fromIntegral (maxBound ∷ Int)
          us' = maxUs `min` us
          rearm passed =
            case us - passed of
              0 → atomically $ writeTVar ttv True
              left → do
                let us'' = maxUs `min` left
                void $ registerTimeout tmm (fromIntegral us'') $
                  rearm $ passed + us''
      void $ registerTimeout tmm (fromIntegral us') $ rearm us'
      return ttv
