{-# LANGUAGE MagicHash #-}
{-
OOHaskell (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

This module gathers the API that we need for OOP in Haskell.  We
basically select a certain configuration of the HList library, and we
also import modules that are needed for mutable data and monads. Note
on overlapping: Needed for the chosen model of labels. Other models
can be used instead, but the chosen look better in types.
-}


module HList where

import Data.STRef
import Data.IORef
import Data.Typeable
import Control.Monad
import Control.Monad.ST
import Control.Monad.Fix
import HArray
import Record
import HListPrelude
import FakePrelude
import GhcSyntax
--import GHC.IOBase hiding (stToIO, writeIORef, readIORef, newIORef, IORef,unsafeIOToST,unsafeSTToIO)

infixr 9 #
(#) :: (HasField l r v) => r -> l -> v
m # field = (m .!. field)

concrete :: (MonadFix m) => (a -> m a) -> a -> m a
concrete generator self = generator self
 where
  _ = mfix generator

