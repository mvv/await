{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Concurrent.Await (
    Attempt(..),
    FromAttempt(..),
    joinAttempt,
    WaitOp(..),
    SomeOp(..),
    MapOp(..),
    NeverOp(..),
    awaitOn,
    await,
    timedAwait,
    awaitEither,
    WaitOps(..),
    (.?), (.?.),
    AIO,
    runAIOs,
    evalAIOs,
    MonadAIO(..)
  ) where

import Prelude hiding (mapM)
import Data.Typeable
import Data.Word (Word)
import Data.List (partition)
import Data.Inject
import Data.Timeout
import Data.Peano
import Data.Heterogeneous.List
import Data.Pointed
import Data.Traversable
import Control.Applicative
import Control.Monad.Base
import Control.Monad.Trans.Reader
import Control.Monad.State.Strict hiding (mapM)
import Control.Monad.Abort hiding (mapM)
import Control.Monad.Exception
import Control.Concurrent.Event
import Control.Concurrent.STM.Hooks
import Control.Concurrent.STM.TFuture

data Attempt α = Success α
               | ∀ e . Exception e ⇒ Failure e
               deriving Typeable

instance Functor Attempt where
  fmap f (Success a) = Success (f a)
  fmap _ (Failure e) = Failure e
  {-# INLINABLE fmap #-}

instance Applicative Attempt where
  pure = Success
  {-# INLINE pure #-}
  Success f <*> Success a = Success (f a)
  Success _ <*> Failure e = Failure e
  Failure e <*> _         = Failure e
  {-# INLINABLE (<*>) #-}

instance Monad Attempt where
  return = pure
  {-# INLINE return #-}
  Success a >>= f = f a
  Failure e >>= _ = Failure e
  {-# INLINABLE (>>=) #-}
  Success _ >> m = m
  Failure e >> _ = Failure e
  {-# INLINABLE (>>) #-}

class FromAttempt f where
  fromAttempt ∷ Attempt α → f α

instance FromAttempt IO where
  fromAttempt (Success a) = return a
  fromAttempt (Failure e) = throwIO e

instance FromAttempt Maybe where
  fromAttempt (Success a) = Just a
  fromAttempt (Failure _) = Nothing

joinAttempt ∷ (Monad μ, FromAttempt μ) ⇒ μ (Attempt α) → μ α
joinAttempt = (>>= fromAttempt)
{-# INLINE joinAttempt #-}

class WaitOp op where
  type WaitOpResult op
  registerWaitOp ∷ (EventHook e ~ IO,
                    StatefulEvent e IO, StatefulEvent e (STMH IO),
                    CompletableEvent e IO, CompletableEvent e (STMH IO),
                    StateHookEvent e IO, StateHookEvent e (STMH IO))
                 ⇒ op → e (Attempt (WaitOpResult op)) → Maybe Timeout
                 → IO Bool
  pollWaitOp ∷ op → IO (Maybe (WaitOpResult op))
  pollWaitOp op = do
    fut ← newTHFutureIO
    void $ awaitOn fut op Just $ Just instantly
    eventIdResult fut >>= \case
      Just (Just a) → Just <$> fromAttempt a
      _ → complete fut Nothing >>= \case
        True  → return Nothing
        False → fmap join $ mapM (mapM fromAttempt) =<< eventIdResult fut

data MapOp r = ∀ op . WaitOp op ⇒ MapOp op (WaitOpResult op → r)

instance WaitOp (MapOp r) where
  type WaitOpResult (MapOp r) = r
  registerWaitOp (MapOp op f) e = registerWaitOp op $ Inject e (fmap f)
  pollWaitOp (MapOp op f) = fmap f <$> pollWaitOp op

data SomeOp r = ∀ op . (WaitOp op, WaitOpResult op ~ r) ⇒ SomeOp op

instance WaitOp (SomeOp r) where
  type WaitOpResult (SomeOp r) = r
  registerWaitOp (SomeOp op) e = registerWaitOp op e
  pollWaitOp (SomeOp op) = pollWaitOp op

data NeverOp r = NeverOp

instance WaitOp (NeverOp r) where
  type WaitOpResult (NeverOp r) = r
  registerWaitOp _ _ _ = return True
  pollWaitOp _ = return Nothing

instance WaitOp op ⇒ WaitOp (Maybe op) where
  type WaitOpResult (Maybe op) = WaitOpResult op
  registerWaitOp Nothing   = const $ const $ return True
  registerWaitOp (Just op) = registerWaitOp op
  pollWaitOp Nothing   = return Nothing
  pollWaitOp (Just op) = pollWaitOp op

data NthException = ∀ e . Exception e ⇒ NthException Word e
                  deriving Typeable

instance Show NthException where
  showsPrec p (NthException n e) = showParen (p > 10) $
    showString "NthException " .
    showsPrec 11 n . showString " " . showsPrec 11 e

instance Exception NthException

instance WaitOp [SomeOp r] where
  type WaitOpResult [SomeOp r] = r
  registerWaitOp ops ev tt = go (0 ∷ Word) ops
    where go _ []          = return True
          go n (op : ops') =
            try (registerWaitOp op (Inject ev $ inj n) tt) >>= \case
              Left e      → do
                c ← complete ev $ inj n $ Failure (e ∷ SomeException)
                return $ c || n /= 0
              Right False → return $ n /= 0
              Right True  → go (n + 1) ops'
          inj _ (Success r) = Success r
          inj n (Failure e) = Failure (NthException n e)

instance WaitOp [MapOp r] where
  type WaitOpResult [MapOp r] = r
  registerWaitOp ops ev tt = go (0 ∷ Word) ops
    where go _ []          = return True
          go n (op : ops') =
            try (registerWaitOp op (Inject ev $ inj n) tt) >>= \case
              Left e      → do
                c ← complete ev $ inj n $ Failure (e ∷ SomeException)
                return $ c || n /= 0
              Right False → return $ n /= 0
              Right True  → go (n + 1) ops'
          inj _ (Success r) = Success r
          inj n (Failure e) = Failure (NthException n e)

awaitOn ∷ (WaitOp op, MonadBase IO μ, EventHook e ~ IO,
           StatefulEvent e IO, StatefulEvent e (STMH IO),
           CompletableEvent e IO, CompletableEvent e (STMH IO),
           StateHookEvent e IO, StateHookEvent e (STMH IO))
        ⇒ e α → op → (Attempt (WaitOpResult op) → α) → Maybe Timeout → μ Bool
awaitOn ev op inj tt = liftBase $ eventState ev >>= \case
  Nothing → mask_ $
    (try $ registerWaitOp op (Inject ev inj) tt) >>= \case
      Right r → return r
      Left  e → complete ev $ inj $ Failure (e ∷ SomeException)
  _ → return False

await ∷ (MonadBase IO μ, WaitOp op) ⇒ op → μ (WaitOpResult op)
await op = liftBase $ do
  fut ← newTHFutureIO
  void $ awaitOn fut op id Nothing
  joinAttempt $ awaitIdResult fut

timedAwait ∷ (MonadBase IO μ, WaitOp op)
           ⇒ op → Timeout → μ (Maybe (WaitOpResult op))
timedAwait op tt = liftBase $ do
  fut ← newTHFutureIO
  void $ awaitOn fut op Just $ Just tt
  timedAwaitIdResult fut tt >>= \case
    Just (Just a) → Just <$> fromAttempt a
    _ → complete fut Nothing >>= \case
      True  → return Nothing
      False → fmap join $ mapM (mapM fromAttempt) =<< eventIdResult fut

data EitherException = ∀ e . Exception e ⇒ LeftException e
                     | ∀ e . Exception e ⇒ RightException e
                     deriving Typeable

instance Show EitherException where
  show (LeftException e) = "LeftException " ++ show e
  show (RightException e) = "RightException " ++ show e

instance Exception EitherException

instance (WaitOp op1, WaitOp op2) ⇒ WaitOp (op1, op2) where
  type WaitOpResult (op1, op2) = Either (WaitOpResult op1) (WaitOpResult op2)
  registerWaitOp (op1, op2) ev tt = do
    let injl (Success r) = Success $ Left r
        injl (Failure e) = Failure (LeftException e)
        injr (Success r) = Success $ Right r
        injr (Failure e) = Failure (RightException e)
    try (registerWaitOp op1 (Inject ev injl) tt) >>= \case
      Left e      → complete ev $ injl $ Failure (e ∷ SomeException)
      Right False → return False
      _ → try (registerWaitOp op2 (Inject ev injr) tt) >>= \case
        Left e  → True <$ complete ev (injr $ Failure (e ∷ SomeException))
        Right _ → return True
  
awaitEither ∷ ∀ op1 op2 μ . (WaitOp op1, WaitOp op2, MonadBase IO μ)
            ⇒ op1 → op2 → μ (Either (WaitOpResult op1) (WaitOpResult op2))
awaitEither = curry await

data WaitOps rs where
  WaitOp ∷ WaitOp op ⇒ op → WaitOps (HSingle (WaitOpResult op))
  (:?)   ∷ (WaitOp op, HNonEmpty rs)
         ⇒ op → WaitOps rs → WaitOps (WaitOpResult op :* rs)

waitOpsNonEmpty ∷ ∀ rs . WaitOps rs → HNonEmptyInst rs
waitOpsNonEmpty (WaitOp _) = HNonEmptyInst
waitOpsNonEmpty (_ :? _)   = HNonEmptyInst

infixr 7 .?
infix  8 .?.

(.?) ∷ WaitOp op ⇒ op → WaitOps rs → WaitOps (WaitOpResult op :* rs)
op .? ops = case waitOpsNonEmpty ops of
  HNonEmptyInst → op :? ops
{-# INLINE (.?) #-}

(.?.) ∷ (WaitOp op1, WaitOp op2) ⇒ op1 → op2
      → WaitOps (WaitOpResult op1 :*: WaitOpResult op2)
op1 .?. op2 = op1 .? WaitOp op2
{-# INLINE (.?.) #-}

data PNthException n e = PNthException (Peano n) e deriving (Typeable, Show)

instance (Typeable n, Exception e) ⇒ Exception (PNthException n e)

{-
awaitMany ∷ ∀ rs μ . MonadBase IO μ ⇒ WaitOps rs → μ (HElemOf rs)
awaitMany ops = liftBase $ case waitOpsNonEmpty ops of
  HNonEmptyInst → case hMapInst ∷ HMapInst Attempt rs of 
    HMapInst → do
      fut ← newTHFutureIO ∷ IO (THFuture IO (HElemOf (HMap Attempt rs)))
      let register ∷ ∀ n . HDropClass n rs
                   ⇒ Peano n → WaitOps (HDrop n rs) → IO ()
          register n (WaitOp op) =
            case hMapDropComm ∷ HMapDropComm Attempt n rs of
              HMapDropComm → void $ awaitOn fut op (HNth n) Nothing
          register n (op :? ops') =
            case hNonEmptyMap ∷ HNonEmptyMap Attempt (HTail (HDrop n rs)) of
              HNonEmptyMap →
                case hMapDropComm ∷ HMapDropComm Attempt n rs of
                  HMapDropComm → do
                    void $ awaitOn fut op (HNth n) Nothing
                    case hTailDropComm ∷ HTailDropComm n rs of
                      HTailDropComm → register (PSucc n) ops'
      register PZero ops
      let mapDropComm ∷ ∀ n
                      . (HDropClass n (HMap Attempt rs),
                         HNonEmpty (HDrop n (HMap Attempt rs)))
                      ⇒ Peano n → HMapDropComm Attempt n rs
          mapDropComm _ =
            case hNextDropInst ∷ HNonEmptyDropInst n (HMap Attempt rs) of
              HNonEmptyDropInst →
                case hMapDropInst (Success ()) ∷ HDropInst n rs of
                  HDropInst → hMapDropComm
          nonEmptyMap ∷ ∀ n
                      . (HDropClass n rs,
                         HDropClass n (HMap Attempt rs),
                         HNonEmpty (HDrop n (HMap Attempt rs)))
                      ⇒ Peano n → HNonEmptyMap Attempt (HDrop n rs)
          nonEmptyMap _ = case hMapDropComm' ∷ HMapDropComm Attempt n rs of
            HMapDropComm → hNonEmptyMap'
      HNth n a ← awaitIdResult fut
      case mapDropComm n of
        HMapDropComm → case nonEmptyMap n of
          HNonEmptyMap → case a of
            Success r → return $ HNth n r
            Failure e → throw $ NthException n e
-}

instance WaitOp (WaitOps rs) where
  type WaitOpResult (WaitOps rs) = HElemOf rs
  registerWaitOp ops ev tt = do
    let inj n (Success r) = Success (HNth n r)
        inj n (Failure e) = Failure (PNthException n e)
        register ∷ ∀ n . HDropClass n rs
                 ⇒ Peano n → WaitOps (HDrop n rs) → IO Bool
        register n (WaitOp op) = eventState ev >>= \case
          Nothing → do
            r ← (try $ registerWaitOp op (Inject ev $ inj n) tt) >>= \case
              Right r → return r
              Left e  → complete ev $ inj n $ Failure (e ∷ SomeException)
            return $ r || not (pZero n)
          _ → return $ not (pZero n)
        register n (op :? ops') = eventState ev >>= \case
          Nothing → do
            (try $ registerWaitOp op (Inject ev $ inj n) tt) >>= \case
              Right True → case waitOpsNonEmpty ops' of
                HNonEmptyInst → case hTailDropComm ∷ HTailDropComm n rs of
                  HTailDropComm → register (PSucc n) ops'
              Right False → return $ not (pZero n)
              Left e → do
                c ← complete ev $ inj n $ Failure (e ∷ SomeException)
                return $ c || not (pZero n)
          _ → return $ not (pZero n)
    case waitOpsNonEmpty ops of
      HNonEmptyInst → register PZero ops

data Prim s α where
  PrimGet  ∷ Prim s s
  PrimSet  ∷ s → Prim s ()
  PrimOp   ∷ WaitOp op ⇒ op → Prim s (WaitOpResult op)
  PrimCond ∷ (s → Bool) → Prim s ()
  PrimFin  ∷ IO (Trace s α) → (Maybe α → AIO s β) → Prim s (α, β) 
  PrimHand ∷ IO (Trace s α) → (SomeException → AIO s α) → Prim s α

data Trace s α where
  TraceExit ∷ Trace s α
  TraceDone ∷ α → Trace s α
  TraceCont ∷ Prim s α → (α → IO (Trace s β)) → Trace s β

data Guard s α β where
  Unguarded ∷ Guard s α α
  Finalizer ∷ Guard s γ β → (α → δ → IO (Trace s γ))
            → (Maybe α → AIO s δ) → Guard s α β
  Catcher   ∷ Guard s γ β → Bool → (α → IO (Trace s γ))
            → (SomeException → AIO s α) → Guard s α β

newtype TraceIO s α = TraceIO (IO (Trace s α))
data OpCont s α = ∀ op . WaitOp op
                ⇒ OpCont op (WaitOpResult op → IO (Trace s α))
data CondCont s α = CondCont (s → Bool) (IO (Trace s α))
  
data Env s c β = ∀ α . Env (Guard s α β) Bool (c s α)

mapEnvCont ∷ (∀ α . c s α → c' s α) → Env s c β → Env s c' β
mapEnvCont f (Env g sp c) = Env g sp (f c)

newtype AIO s α = AIO { runAIO ∷ ∀ β . (α → IO (Trace s β)) → IO (Trace s β) }

trace ∷ AIO s α → IO (Trace s α)
trace (AIO g) = g (return . TraceDone)

traceIO ∷ AIO s α → TraceIO s α
traceIO = TraceIO . trace

runAIOs ∷ ∀ s μ α . MonadBase IO μ ⇒ s → [AIO s α] → μ (s, Maybe (Attempt α))
runAIOs s0 ms = liftBase $ mask_ $
    go s0 False Nothing (Env Unguarded False . traceIO <$> ms) [] []
  where
    go ∷ s → Bool → Maybe (Attempt α)
       → [Env s TraceIO α] → [Env s OpCont α] → [Env s CondCont α]
       → IO (s, Maybe (Attempt α))
    go s sc mbr (Env g sp (TraceIO m) : cs) opCs condCs = try m >>= \case
      Left e → case g of
        Unguarded → case mbr of
          Just _  → go s sc mbr cs opCs condCs
          Nothing → go s sc (Just $ Failure e) (map cv opCs ++ map cv condCs) [] []
            where cv ∷ ∀ c . Env s c α → Env s TraceIO α
                  cv (Env g' sp' _) = Env g' sp' (traceIO aioExit)
        Finalizer g' _ fin →
          go s sc mbr (Env g' sp (traceIO $ fin Nothing >> throw e) : cs) opCs condCs
        Catcher g' sp' cont h →
          if sp' /= sp
            then go s sc mbr (Env g' sp (traceIO aioExit) : cs) opCs condCs
            else go s sc mbr (Env g' sp (TraceIO $ runAIO (h e) cont) : cs) opCs condCs
      Right TraceExit → case g of
        Unguarded →
          go s sc mbr cs opCs condCs
        Finalizer g' _ fin →
          go s sc mbr (Env g' True (traceIO $ fin Nothing >> aioExit) : cs) opCs condCs
        Catcher g' _ _ _ →
          go s sc mbr (Env g' True (traceIO $ aioExit) : cs) opCs condCs
      Right (TraceDone a) → case g of
        Unguarded → case mbr of
          Just _  → go s sc mbr cs opCs condCs
          Nothing → go s sc (Just $ Success a) (map cv cs ++ map cv opCs ++ map cv condCs) [] []
            where cv ∷ ∀ c . Env s c α → Env s TraceIO α
                  cv (Env g' sp' _) = Env g' sp' (traceIO aioExit)
        Finalizer g' cont fin →
          go s sc mbr (Env g' sp (TraceIO $ runAIO (fin $ Just a) (cont a)) : cs) opCs condCs
        Catcher g' _ cont _ →
          go s sc mbr (Env g' sp (TraceIO $ cont a) : cs) opCs condCs
      Right (TraceCont prim cont) → case prim of
        PrimGet →
          go s sc mbr (Env g sp (TraceIO $ cont s) : cs) opCs condCs
        PrimSet s' →
          go s' True mbr (Env g sp (TraceIO $ cont ()) : cs) opCs condCs
        PrimOp op →
          go s sc mbr cs (Env g sp (OpCont op cont) : opCs) condCs
        PrimCond cond →
          if cond s
            then go s sc mbr (Env g sp (TraceIO $ cont ()) : cs) opCs condCs
            else go s sc mbr cs opCs (Env g sp (CondCont cond $ cont ()) : condCs)
        PrimHand body h →
          go s sc mbr (Env (Catcher g sp cont h) sp (TraceIO body) : cs) opCs condCs
        PrimFin body fin →
          go s sc mbr (Env (Finalizer g (curry cont) fin) sp (TraceIO body) : cs) opCs condCs
    go s True mbr [] opCs condCs =
        go s False mbr cs opCs noCs
      where (yesCs, noCs) = partition (\(Env _ _ (CondCont cond _)) → cond s) condCs
            cs = map (mapEnvCont (\(CondCont _ cont) → TraceIO cont)) $ reverse yesCs
    go s False mbr [] [] [] =
      return (s, mbr)
    go s False mbr [] [] condCs =
      go s False (maybe (Just $ Failure Deadlock) Just mbr)
                 (map (\(Env g' sp' _) → Env g' sp' (traceIO aioExit)) condCs)
                 [] []
    go s False mbr [] opCs condCs = do
      let opCs' = reverse opCs
          deleteNth ∷ Word → [β] → [β]
          deleteNth n ls = fmap fst $ filter ((/= n) . snd) $ zip ls [0..]
          mkCont (Env g sp (OpCont op cont)) n = MapOp op $ \r →
            go s False mbr [Env g sp (TraceIO $ cont r)]
                           (deleteNth n opCs') condCs 
      try (await $ map (uncurry mkCont) $ zip opCs' [0..]) >>= \case
        Left (NthException n e) → do
          go s False mbr
            [mapEnvCont (const $ TraceIO $ throw e) $ opCs' !! fromIntegral n]
            (deleteNth n opCs') condCs
        Right cont →
          cont

evalAIOs ∷ MonadBase IO μ ⇒ s → [AIO s α] → μ (Maybe α)
evalAIOs s = liftBase . (mapM fromAttempt =<<) . fmap snd . runAIOs s

instance Pointed (AIO s) where
  point a = AIO ($ a)

instance Functor (AIO s) where
  fmap f (AIO g) = AIO $ \c → g (c . f)

instance Applicative (AIO s) where
  pure  = point
  (<*>) = ap

instance Monad (AIO s) where
  return      = point
  AIO g >>= f = AIO $ \c → g (\a → runAIO (f a) c)

instance MonadBase IO (AIO s) where
  liftBase io = AIO (io >>=)

instance MonadAbort SomeException (AIO s) where
  abort = liftBase . throw 

instance MonadRecover SomeException (AIO s) where
  recover m h = AIO $ return . TraceCont (PrimHand (trace m) h)

instance MonadFinally (AIO s) where
  finally' m f = AIO $ return . TraceCont (PrimFin (trace m) f)

{-
instance MonadMask () (AIO s) where
  getMaskingState = return ()
  withMaskingState = const id
  -}

instance MonadState s (AIO s) where
  get   = AIO $ return . TraceCont PrimGet
  put s = AIO $ return . TraceCont (PrimSet s)

class (MonadBase IO μ, MonadState s μ) ⇒ MonadAIO s μ | μ → s where
  aioExit  ∷ μ α
  aioAfter ∷ (s → Bool) → μ ()
  aioAwait ∷ WaitOp op ⇒ op → μ (WaitOpResult op)

instance MonadAIO s (AIO s) where
  aioExit       = AIO $ const $ return TraceExit
  aioAfter cond = AIO $ return . TraceCont (PrimCond cond)
  aioAwait op   = AIO $ return . TraceCont (PrimOp op)

instance MonadAIO s μ ⇒ MonadAIO s (ReaderT r μ) where
  aioExit  = lift aioExit
  aioAfter = lift . aioAfter
  aioAwait = lift . aioAwait

