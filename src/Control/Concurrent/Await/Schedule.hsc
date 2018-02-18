{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Concurrent.Await.Schedule
  ( Schedule
  , ScheduleKey
  , newSchedule
  , scheduleAfter
  , unschedule
  , aioSleep
  ) where

import Data.Word (Word64)
import Data.Int (Int64)
import Data.Timeout
import Data.Maybe (isJust)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Function (on)
import Data.Inject
import Data.Foldable (forM_)
import Control.Applicative
import Control.Monad (void, when)
import Control.Monad.Base
import Control.Monad.Trans.Class (lift)
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar
import Control.Concurrent.STM.Lifted
import Control.Concurrent.STM.Hooks
import Control.Concurrent.STM.Rollback
import Control.Concurrent.STM.TWaitQueue (TWaitQueue)
import qualified Control.Concurrent.STM.TWaitQueue as TWQ
import Control.Concurrent.Event
import Control.Concurrent.Await
import System.Posix.Clock
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)
import GHC.Event
import Internal.Control

#include <HsBaseConfig.h>

data SomeCE α = ∀ e . CompletableEvent e (STMH IO) ⇒ SomeCE (e α)

data ScheduleSt α = ScheduleSt { schNext  ∷ !Int
                               , schMin   ∷ !Word64
                               , schMap   ∷ Map Word64 [(Int, α)]
                               , schN     ∷ !Int
                               }

data ScheduleCb = NoCb
                | RegisteredCb Word64 (Maybe TimeoutKey)

data Schedule α = Schedule { schId    ∷ !Word64
                           , schSt    ∷ !(TVar (ScheduleSt α))
                           , schCb    ∷ !(MVar (Int, ScheduleCb))
                           , schQueue ∷ !(TWaitQueue (SomeCE α) ())
                           }

instance Eq (Schedule α) where
  (==) = on (==) schSt

instance Show (Schedule α) where
  show (Schedule {schId}) = "<<Scheduler #" ++ show schId ++ ">>"

data ScheduleKey = ∀ α . ScheduleKey { schR    ∷ !(Schedule α)
                                     , schTime ∷ !Word64
                                     , schKey  ∷ !Int
                                     }

schIdVar ∷ TVar Word64
schIdVar = unsafePerformIO (newTVarIO 0)
{-# NOINLINE schIdVar #-}

newSchedule ∷ MonadBase IO μ ⇒ μ (Schedule α)
newSchedule = liftBase $ do
  let st = ScheduleSt { schNext  = 0
                      , schMap   = Map.empty
                      , schMin   = 0
                      , schN     = 0
                      }
  sid ← atomically $ do
    i ← readTVar schIdVar
    writeTVar schIdVar $! i + 1
    return i
  Schedule sid <$> newTVarIO st <*> newMVar (0, NoCb) <*> TWQ.emptyIO

getMicros ∷ MonadBase IO μ ⇒ μ Word64
getMicros = do
  (s, ns) ← timeSpecV <$> getClockTime realtimeClock
#if HTYPE_TIME_T == Int64
  let s' = unsafeCoerce s ∷ Int64 
#elif HTYPE_TIME_T == Int32
  let s' = unsafeCoerce s ∷ Int32
#else
# error unexpected HTYPE_TIME_T value
#endif
  return $ fromIntegral s' * 1000000 + fromIntegral ns `quot` 1000

syncCallback ∷ MonadBase IO μ ⇒ Schedule α → Maybe Int → Word64 → μ ()
syncCallback sch@(Schedule {..}) mSq now = liftBase $ do
#if MIN_VERSION_base(4,7,0)
    tmm ← getSystemTimerManager
#else
    Just tmm ← getSystemEventManager
#endif
    modifyMVar_' schCb $ \(sq, cb) → do
      (ScheduleSt {..}, isEmpty) ← atomically $
        (,) <$> readTVar schSt <*> TWQ.nullOrFinished schQueue
      if schN == 0 || isEmpty
      then case cb of
        NoCb →
          return (sq, NoCb)
        RegisteredCb _ mTk → do
          when (mSq /= Just sq) $
            forM_ mTk $ liftBase . unregisterTimeout tmm
          return (sq + 1, NoCb)
      else case cb of
        NoCb →
          (sq, ) . RegisteredCb schMin <$> reg tmm sq schMin
        RegisteredCb _ _ | mSq == Just sq →
          (sq, ) . RegisteredCb schMin <$> reg tmm sq schMin
        RegisteredCb at _ | at <= schMin → do
          return (sq, cb)
        RegisteredCb _ mTk → do
          forM_ mTk $ liftBase . unregisterTimeout tmm
          let !sq' = sq + 1
          (sq', ) . RegisteredCb schMin <$> reg tmm sq' schMin
  where
    reg tmm sq at =
      if at <= now
      then do
        void $ forkIO $ doCallback sch sq now
        return Nothing
      else do
        let us = fromIntegral (maxBound ∷ Int) `min` (at - now)
        fmap Just $ registerTimeout tmm (fromIntegral us) $ do
          now' ← getMicros
          if now' < at
          then syncCallback sch (Just sq) now'
          else doCallback sch sq now'

doCallback ∷ Schedule α → Int → Word64 → IO ()
doCallback sch@(Schedule {..}) sq now = do
  let doWhile m = m >>= \c → if c then doWhile m else return ()
  doWhile $ atomicallyHR $ do
    st@(ScheduleSt {..}) ← readTVar schSt
    rollbackUnless False $ schN > 0 && schMin <= now
    someEv ← TWQ.dequeue schQueue >>= \case
      Right (Just ev) → return ev
      _ → rollback False
    let Just ((_, v) : vs, m) = Map.minView schMap
    completed ← case someEv of
      SomeCE ev → lift $ complete ev v
    when completed $
      writeTVar schSt $!
        if null vs then
          st { schMap = m
             , schMin = if schN == 1 then 0 else fst $ Map.findMin m
             , schN   = schN - 1 }
        else
          st { schMap = Map.updateMin (const $ Just vs) schMap
             , schN   = schN - 1 }
    return True
  syncCallback sch (Just sq) now

schedule' ∷ MonadBase IO μ ⇒ Schedule α → Word64 → Word64 → α → μ ScheduleKey
schedule' sch@(Schedule {..}) now at what = do
  (key, needSync) ← atomically $ do
    st@(ScheduleSt {..}) ← readTVar schSt
    let key   = ScheduleKey { schR = sch, schTime = at, schKey = schNext }
        value = [(schNext, what)]
    if schN > 0 && at >= schMin
    then do
      writeTVar schSt $
        st { schNext = schNext + 1
           , schMap  = Map.insertWith' ((:) . head) at value schMap
           , schN    = schN + 1 }
      return (key, False)
    else do
      writeTVar schSt $
        st { schNext = schNext + 1
           , schMap  = Map.insert at value schMap
           , schMin  = at
           , schN    = schN + 1 }
      (key, ) . not <$> TWQ.nullOrFinished schQueue
  when needSync $
    syncCallback sch Nothing now
  return key

scheduleAfter ∷ MonadBase IO μ ⇒ Schedule α → Timeout → α → μ ScheduleKey
scheduleAfter sch tt a = do
  now ← getMicros
  schedule' sch now (now + tt #> MicroSecond) a

unschedule ∷ MonadBase IO μ ⇒ ScheduleKey → μ Bool
unschedule (ScheduleKey {..}) = do
  let Schedule {..} = schR
  (unscheduled, needSync) ← atomically $ do
    st@(ScheduleSt {..}) ← readTVar schSt
    case Map.lookup schTime schMap of
      Just xs | isJust (lookup schKey xs) → do
        let xs' = filter ((/= schKey) . fst) xs
        isEmpty ← TWQ.nullOrFinished schQueue
        let needSync = null xs' && schTime == schMin && not isEmpty
        writeTVar schSt $!
          if null xs'
            then
              let m = Map.delete schTime schMap in
                st { schMap = m
                   , schMin = if schTime == schMin
                                then if schN == 1
                                       then 0
                                       else fst $ Map.findMin m
                                else schMin
                   , schN   = schN - 1 }
            else st { schMap = Map.insert schTime xs' schMap
                    , schN   = schN - 1 }
        return (True, needSync)
      _ → return (False, False)
  when needSync $ do
    now ← getMicros
    syncCallback schR Nothing now
  return unscheduled

instance WaitOp (Schedule α) where
  type WaitOpResult (Schedule α) = α
  registerWaitOp sch@(Schedule {..}) ev _ = do
    (r, needSync) ← atomicallyHR $ do
      wasEmpty ← TWQ.nullOrFinished schQueue
      Right key ← TWQ.enqueue schQueue $ SomeCE $ Inject ev Success
      (rollbackUnless (False, False) =<<) $
        lift $ onEvent ev $ const $ atomically $ TWQ.delete schQueue key
      if wasEmpty then do
        ScheduleSt {..} ← readTVar schSt
        return (True, schN /= 0)
      else
        return (True, False)
    when needSync $ do
      now ← getMicros
      syncCallback sch Nothing now
    return r

aioSleep ∷ MonadAIO s μ ⇒ Timeout → μ ()
aioSleep tt = do
  sch ← newSchedule
  void $ scheduleAfter sch tt ()
  aioAwait sch

