{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Concurrent.Await.Service (
    ServiceResetError(..),
    ServiceStoppedError(..),
    ServiceCaps,
    Service,
    newService,
    ServiceReq,
    ServiceResp,
    ServiceReqResp(..),
    request,
    requestOnChan,
    forward,
    respond,
    resetService,
    stopService,
    ServicePoll,
    poll,
    rearm
  ) where

import Prelude hiding (mapM, mapM_)
import Data.Typeable (Typeable)
import Data.Word (Word64)
import Data.Maybe (fromMaybe)
import Data.Inject
import Data.Heterogeneous.List
import Data.Capability
import Data.Bifunctor
import Data.Traversable (mapM)
import Data.Foldable (mapM_)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad hiding (mapM, mapM_)
import Control.Monad.Base
import Control.Monad.Trans.Class
import Control.Monad.Exception
import Control.Concurrent.MVar
import Control.Concurrent.STM.Lifted
import Control.Concurrent.STM.Rollback
import Control.Concurrent.STM.Hooks
import Control.Concurrent.STM.TWaitQueue (TWaitQueue)
import qualified Control.Concurrent.STM.TWaitQueue as TWQ
import Control.Concurrent.Event
import Control.Concurrent.Await
import Control.Concurrent.Await.OneShot
import Control.Concurrent.Await.Chan
import Internal.Control

--data SomeIOCE α = ∀ e . CompletableEvent e IO ⇒ SomeIOCE (e (Attempt α))
newtype SomeIOCE α = SomeIOCE (Attempt α → IO Bool)

data SomeTCE p = ∀ e . CompletableEvent e (STMH IO)
               ⇒ SomeTCE (e (Attempt (ServiceReqResp p)))

data ServiceResetError = ServiceResetError deriving (Typeable, Show)

instance Exception ServiceResetError

data ServiceStoppedError = ServiceStoppedError deriving (Typeable, Show)

instance Exception ServiceStoppedError

type ServiceCaps = ReadCap :*: WriteCap

data Service p caps =
  Service { serviceReqs     ∷ !(TWaitQueue (ServiceIn p) ())
          , serviceHandlers ∷ !(TWaitQueue (SomeTCE p) ())
          , serviceEpoch    ∷ !(TVar Word64)
          , serviceNextKey  ∷ !(TVar Word64)
          , serviceHandling ∷ !(TVar (Map Word64 (ServiceIn p)))
          }

instance Restrict (Service p) where
  restrict (Service {..}) = Service serviceReqs serviceHandlers
                                    serviceEpoch serviceNextKey
                                    serviceHandling

newService ∷ MonadBase IO μ ⇒ μ (Service p ServiceCaps)
newService = Service <$> TWQ.emptyIO <*> TWQ.emptyIO
                     <*> newTVarIO 0 <*> newTVarIO 0 <*> newTVarIO Map.empty

data ServiceReq resp = ∀ p caps
                     . ServiceReq !(Service p caps)
                                  {-# UNPACK #-} !Word64 -- Epoch
                                  {-# UNPACK #-} !Word64 -- Key
                                  !(TWaitQueue (SomeIOCE resp) (Attempt resp))
newtype ServiceResp resp =
  ServiceResp (TWaitQueue (SomeIOCE resp) (Attempt resp))

data ServiceIn p = ∀ resp
                 . ServiceIn !(p resp)
                             {-# UNPACK #-} !Word64 -- Key
                             !(TWaitQueue (SomeIOCE resp) (Attempt resp))

data ServiceReqResp p = ∀ resp . (p resp) :⊳: (ServiceReq resp)

request ∷ (MonadBase IO μ, WriteCap :∈: caps)
        ⇒ Service p caps → p resp → μ (ServiceResp resp)
request srv@(Service {..}) req = liftBase $ mask_ $ do
  wq ← TWQ.emptyIO
  key ← atomically $ do
    key ← readTVar serviceNextKey
    writeTVar serviceNextKey $! key + 1
    return key
  atomicallyH $ do
    epoch ← readTVar serviceEpoch
    add ← TWQ.null serviceReqs >>= \case
      Right True → go
        where go = TWQ.dequeue serviceHandlers >>= \case
                     Right (Just (SomeTCE ev)) → do
                       let rr = req :⊳: ServiceReq srv epoch key wq
                       complete ev (Success rr) >>= \case
                         True → do
                           handling ← readTVar serviceHandling
                           writeTVar serviceHandling $!
                             Map.insert key (ServiceIn req key wq) handling
                           return False
                         False → go
                     _ → return True
      Right False → return True
      _ → throw ServiceStoppedError
    when add $ void $ TWQ.enqueue serviceReqs $ ServiceIn req key wq
  return $ ServiceResp wq

requestOnChan ∷ (MonadBase IO μ, WriteCap :∈: caps, WriteCap :∈: cc)
              ⇒ Service p caps → p resp → Chan cc α → (Attempt resp → α)
              → μ Bool
requestOnChan srv req chan f = liftBase $ mask_ $ do
  ServiceResp wq ← request srv req
  let comp = SomeIOCE $ (True <$) . writeChanAsync chan . f
  atomically (TWQ.enqueue wq comp) >>= \case
    Left resp → do
      writeChanAsync chan $ f resp
      return False
    Right _   → return True

forward ∷ (MonadBase IO μ, WriteCap :∈: caps)
        ⇒ ServiceReq resp → Service p' caps → p' resp' → (resp' → resp)
        → μ Bool
forward req srv' req' f = liftBase $ mask_ $ do
  ServiceResp wq' ← request srv' req'
  atomically (TWQ.enqueue wq' (SomeIOCE $ respond' req . fmap f)) >>= \case
    Left resp → respond' req $ fmap f resp 
    Right _   → return True
  
respond' ∷ MonadBase IO μ ⇒ ServiceReq resp → Attempt resp → μ Bool
respond' (ServiceReq (Service {..}) epoch key wq) resp = liftBase $ mask_ $ do
  (r, evs) ← atomicallyR $ do
    (rollbackUnless (False, []) =<<) $ (== epoch) <$> readTVar serviceEpoch
    TWQ.finish wq resp >>= \case
      Just evs → do
        handling ← readTVar serviceHandling
        writeTVar serviceHandling $! Map.delete key handling
        return (True, evs)
      Nothing → return (False, [])
  forM_ evs $ \(SomeIOCE ev) → ev resp
  return r

respond ∷ MonadBase IO μ ⇒ ServiceReq resp → resp → μ Bool
respond req = respond' req . Success

instance (ReadCap :∈: caps) ⇒ WaitOp (Service p caps) where
  type WaitOpResult (Service p caps) = ServiceReqResp p
  registerWaitOp srv@(Service {..}) ev _ = atomicallyHR $ do
    add ← TWQ.nullOrFinished serviceHandlers >>= \case
      True → TWQ.dequeue serviceReqs >>= \case
        Right (Just srvIn@(ServiceIn req key wq)) → do
          epoch ← readTVar serviceEpoch
          (rollbackUnless False =<<) $ lift $ complete ev $ Success $
            req :⊳: ServiceReq srv epoch key wq
          handling ← readTVar serviceHandling
          writeTVar serviceHandling $! Map.insert key srvIn handling
          return False
        Right Nothing → return True
        Left _ → return False
      False → return True
    when add $ do
      Right key ← TWQ.enqueue serviceHandlers $ SomeTCE ev
      (rollbackUnless False =<<) $ lift $
        onEvent ev $ const $ atomically $ TWQ.delete serviceHandlers key
    return True

instance WaitOp (ServiceResp resp) where
  type WaitOpResult (ServiceResp resp) = resp
  registerWaitOp (ServiceResp wq) ev _ = atomicallyHR $ do
    TWQ.enqueue wq (SomeIOCE $ complete ev) >>= \case
      Right key → do
        (rollbackUnless False =<<) $
          lift $ onEvent ev $ const $ atomically $ TWQ.delete wq key
        return True
      Left r → lift $ complete ev r
  pollWaitOp (ServiceResp wq) = mapM fromAttempt =<< TWQ.resultIO wq

resetService ∷ MonadBase IO μ ⇒ Service p caps → μ ()
resetService (Service {..}) = liftBase $ mask_ $ do
  Right handlers ← atomicallyH $ do
    epoch ← (+ 1) <$> readTVar serviceEpoch
    writeTVar serviceEpoch $! epoch
    handling ← fmap snd . Map.toDescList <$> readTVar serviceHandling
    writeTVar serviceHandling $! Map.empty
    (TWQ.prepend serviceReqs handling >>=) $ mapM_ $ const $
      throw ServiceStoppedError
    TWQ.dequeueAll serviceHandlers
  forM_ handlers $ \(SomeTCE ev) →
    void $ atomicallyH $ complete ev $ Failure ServiceResetError

stopService ∷ MonadBase IO μ ⇒ Service p caps → μ Bool
stopService (Service {..}) = liftBase $ do
  (r, reqs) ← atomically $ TWQ.finish serviceReqs () >>= \case
    Just reqs → return (True, reqs)
    Nothing → return (False, [])
  let resp = Failure ServiceStoppedError
  forM_ reqs $ \(ServiceIn _ _ wq) → do
    evs ← atomically $ fromMaybe [] <$> TWQ.finish wq resp
    forM_ evs $ \(SomeIOCE ev) → ev resp
  return r

data ServicePoll α = ∀ p scs ocs . (WriteCap :∈: scs, ReadCap :∈: ocs)
                   ⇒ ServicePoll
                       { pollService ∷ Service p scs
                       , pollReq     ∷ p (α, OneShot ocs α)
                       , pollOp      ∷ MVar (SomeOp (α, Maybe (SomeOp α)))
                       }

poll ∷ (WriteCap :∈: scs, ReadCap :∈: ocs, MonadBase IO μ)
     ⇒ Service p scs → p (α, OneShot ocs α) → μ (ServicePoll α)
poll s r = liftBase $ do
  req ← request s r
  ServicePoll s r <$>
    newMVar (SomeOp $ MapOp req $ second $ Just . SomeOp)

rearm ∷ MonadBase IO μ ⇒ ServicePoll α → μ ()
rearm (ServicePoll {..}) = liftBase $ modifyMVar_' pollOp $ \op →
  pollWaitOp op >>= \case
    Just (_, Nothing) → do
      req ← request pollService pollReq
      return $ SomeOp $ MapOp req $ second $ Just . SomeOp
    Just (_, Just o) →
      return $ SomeOp $ MapOp o (, Nothing)
    Nothing →
      return op

instance WaitOp (ServicePoll α) where
  type WaitOpResult (ServicePoll α) = α
  registerWaitOp (ServicePoll {pollOp}) ev tt =
    withMVar pollOp $ \op →
      registerWaitOp op (Inject ev (fmap fst)) tt

