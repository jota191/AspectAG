{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE DataKinds,
             TypeOperators,
             PolyKinds,
             GADTs,
             TypeInType,
             RankNTypes,
             StandaloneDeriving,
             FlexibleInstances,
             FlexibleContexts,
             ConstraintKinds,
             MultiParamTypeClasses,
             FunctionalDependencies,
             UndecidableInstances,
             ScopedTypeVariables,
             TypeFamilies,
             InstanceSigs,
             AllowAmbiguousTypes,
             TypeApplications,
             PatternSynonyms
#-}

module Language.Grammars.AspectAG.Require where

import Data.Kind
import Data.Proxy
import GHC.TypeLits
import Language.Grammars.AspectAG.TPrelude
import Data.Type.Equality

class Require (op   :: Type)
              (ctx  :: [ErrorMessage])  where
   type ReqR op :: Type
   req :: Proxy ctx -> op -> ReqR op

instance (TypeError (Text "Error: " :<>: m :$$:
                     Text "trace: " :<>: ShowCTX ctx))
  => Require (OpError m) ctx where {}

data OpError (m :: ErrorMessage) where {}

type family ShowCTX (ctx :: [ErrorMessage]) :: ErrorMessage where
  ShowCTX '[] = Text ""
  ShowCTX (m ': ms) = m :$$: ShowCTX ms


type family ShowEM (m :: ErrorMessage) :: ErrorMessage

type family ShowT (t :: k) :: ErrorMessage
type instance ShowT (t :: Type) = ShowType t
{-
Abro esta familia para poder definirla de manera extensible, porque no sabemos
en GenReord como se muestran los tipos para instancias concretas. El problema es
que estaba definida con un pattern que capturaba todos los demas casos al final
y en tf cerradas no se admite overlap. Entonces defino aca una instancia para el
kind t (era a fin de cuentas lo que caia en el último pattern)
-}

type RequireR (op :: Type ) (ctx:: [ErrorMessage]) (res :: Type)
     = (Require op ctx, ReqR op ~ res)


type RequireEq (t1 :: k )(t2 :: k) (ctx:: [ErrorMessage])
    = (Require (OpEq t1 t2) ctx, t1 ~ t2)

data OpEq t1 t2

instance RequireEqRes t1 t2 ctx
  => Require (OpEq t1 t2) ctx where
  type ReqR (OpEq t1 t2) = ()
  req = undefined

type family RequireEqRes (t1 :: k) (t2 :: k)
                     (ctx :: [ErrorMessage]) ::  Constraint where
  RequireEqRes t1 t2 ctx = If (t1 `Equal` t2) (() :: Constraint)
    (Require (OpError (Text "" :<>: ShowT t1 :<>: Text " /= " :<>: ShowT t2)) ctx)

