{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, EmptyDataDecls #-}
{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Yet another model of labels.
   Labels are type proxies.
-}

module Data.HList.Label4 where

import Data.Typeable
import Data.Char

import Data.HList.FakePrelude
import Data.HList.Record


-- Equality on labels

instance TypeEq x y b => HEq (Proxy x) (Proxy y) b


-- Show label

instance Typeable x => ShowLabel (Proxy x)
 where
  showLabel = (\(x:xs) -> toLower x:xs)
            . reverse
            . takeWhile (not . (==) '.')
            . reverse
            . show
{-
            . tyConString
            . typeRepTyCon
-}
            . typeOf
            . unProxy
