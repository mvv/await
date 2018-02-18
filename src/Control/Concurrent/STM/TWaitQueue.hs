{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Concurrent.STM.TWaitQueue (
    Key,
    TWaitQueue,
    empty,
    emptyIO,
    null,
    nullOrFinished,
    enqueue,
    prepend,
    dequeue,
    dequeueAll,
    delete,
    finish,
    result,
    resultIO
  ) where

import Prelude hiding (null)
import Data.Word (Word64)
import Data.Bifunctor
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative ((<$>))
import Control.Monad.Base
import Control.Category ((<<<))
import Control.Arrow ((&&&))
import Control.Concurrent.STM.Lifted

newtype Key = Key Word64 deriving (Eq, Ord, Show)
data State α = State { stNextKey ∷ {-# UNPACK #-} !Word64
                     , stMap     ∷ Map Word64 α
                     , stPrefix  ∷ [α]
                     }
newtype TWaitQueue α r = TWaitQueue (TVar (Either r (State α)))

instance Eq (TWaitQueue α r) where
  (TWaitQueue v) == (TWaitQueue v') = v == v'
  {-# INLINE (==) #-}

empty ∷ MonadBase STM μ ⇒ μ (TWaitQueue α r)
empty = fmap TWaitQueue $ newTVar $ Right $
          State { stNextKey = 0
                , stMap     = Map.empty
                , stPrefix  = []
                }
{-# INLINE empty #-}

emptyIO ∷ MonadBase IO μ ⇒ μ (TWaitQueue α r)
emptyIO = fmap TWaitQueue $ newTVarIO $ Right $
            State { stNextKey = 0
                  , stMap     = Map.empty
                  , stPrefix  = []
                  }
{-# INLINE emptyIO #-}

null ∷ MonadBase STM μ ⇒ TWaitQueue α r → μ (Either r Bool)
null (TWaitQueue v) =
  second (uncurry (&&) <<< Map.null . stMap &&& List.null . stPrefix) <$>
    readTVar v
{-# INLINE null #-}

nullOrFinished ∷ MonadBase STM μ ⇒ TWaitQueue α r → μ Bool
nullOrFinished (TWaitQueue v) =
  either (const True)
         (uncurry (&&) <<< Map.null . stMap &&& List.null . stPrefix) <$>
    readTVar v
{-# INLINE nullOrFinished #-}

enqueue ∷ MonadBase STM μ ⇒ TWaitQueue α r → α → μ (Either r Key)
enqueue (TWaitQueue v) e = readTVar v >>= \case
  Right st@(State {..}) → do
    writeTVar v $ Right $ st { stNextKey = stNextKey + 1
                             , stMap     = Map.insert stNextKey e stMap }
    return $ Right $ Key stNextKey
  Left r →
    return $ Left r

prepend ∷ MonadBase STM μ ⇒ TWaitQueue α r → [α] → μ (Maybe r)
prepend (TWaitQueue v) [] = either Just (const Nothing) <$> readTVar v
prepend (TWaitQueue v) xs = readTVar v >>= \case
  Right st@(State {..}) → do
    let !prefix = if List.null stPrefix then xs else xs ++ stPrefix
    writeTVar v $ Right $ st { stPrefix = prefix }
    return Nothing
  Left r →
    return $ Just r

dequeue ∷ MonadBase STM μ ⇒ TWaitQueue α r → μ (Either r (Maybe α))
dequeue (TWaitQueue v) = readTVar v >>= \case
  Right st@(State {..}) → case stPrefix of
    [] → case Map.minView stMap of
      Nothing → return $ Right $ Nothing
      Just (e, m) → do
        writeTVar v $ Right $ st { stMap = m }
        return $ Right $ Just $ e
    (e : prefix) → do
      writeTVar v $ Right $ st { stPrefix = prefix }
      return $ Right $ Just e
  Left r →
    return $ Left r

dequeueAll ∷ MonadBase STM μ ⇒ TWaitQueue α r → μ (Either r [α])
dequeueAll (TWaitQueue v) = readTVar v >>= \case
  Right st@(State {..}) → do
    writeTVar v $ Right $ st { stMap = Map.empty, stPrefix = [] }
    return $ Right $ stPrefix ++ Map.elems stMap
  Left r →
    return $ Left r

delete ∷ MonadBase STM μ ⇒ TWaitQueue α r → Key → μ Bool
delete (TWaitQueue v) (Key key) = readTVar v >>= \case
  Right st@(State {..}) →
    case Map.updateLookupWithKey (const $ const Nothing) key stMap of
      (Nothing, _) → return False
      (Just _, m) → do
        writeTVar v $ Right $ st { stMap = m }
        return True
  _ → return False

finish ∷ MonadBase STM μ ⇒ TWaitQueue α r → r → μ (Maybe [α])
finish (TWaitQueue v) r = readTVar v >>= \case
  Right (State {..}) → do
    writeTVar v $ Left r
    return $ Just $ stPrefix ++ Map.elems stMap
  _ → return Nothing

result ∷ MonadBase STM μ ⇒ TWaitQueue α r → μ (Maybe r)
result (TWaitQueue v) = either Just (const Nothing) <$> readTVar v

resultIO ∷ MonadBase IO μ ⇒ TWaitQueue α r → μ (Maybe r)
resultIO (TWaitQueue v) = either Just (const Nothing) <$> readTVarIO v

