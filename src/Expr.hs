
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE UnicodeSyntax             #-}

module Expr where
import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.RecordInstances

import Data.Type.Require hiding (emptyCtx, ShowTE)

import Data.GenRec hiding (Label)
import Data.GenRec.Label

import Data.Kind
import Data.Proxy
import GHC.TypeLits

import Data.Maybe
import Data.Type.Equality
import Control.Monad.Reader

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Either
import Data.Singletons.CustomStar
import Data.Singletons.Decide

-----------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
type Nt_Expr = 'NT "Expr"
expr = SNT SSym:: Sing Nt_Expr

type P_Add = 'Prd "p_Add" Nt_Expr
add = SPrd SSym expr :: Sing P_Add

type P_Val = 'Prd "p_Val" Nt_Expr
val = SPrd SSym expr :: Sing P_Val

type P_Var = 'Prd "p_Var" Nt_Expr
var = SPrd SSym expr :: Sing P_Var

leftAdd :: Sing ('Chi "leftAdd"   P_Add ('Left Nt_Expr))
leftAdd = SChi SSym add (SLeft $ SNT SSym)

rightAdd :: Sing ('Chi "rightAdd"   P_Add ('Left Nt_Expr))
rightAdd = SChi SSym add (SLeft $ SNT SSym)

ival :: Sing ('Chi "ival"      P_Val ('Right ('T Integer)))
ival = SChi SSym val (SRight $ ST sing)

vname :: Sing ('Chi "vname"     P_Var ('Right ('T String)))
vname = SChi SSym var (SRight $ ST undefined) -- TODO

eval :: Sing ('Att "eval" Integer)
eval = SAtt SSym sing
env  :: Sing ('Att "env"  [(String, Integer)])
env  = SAtt SSym sing
data Expr = Val Integer
          | Var String
          | Add Expr Expr
       deriving Show



sem_Expr asp (Add l r) = knitAspect add asp
                           $  leftAdd  .=. sem_Expr asp l
                          .*. rightAdd .=. sem_Expr asp r
                          .*.  EmptyRec
sem_Expr asp (Val i)   = knitAspect val asp$
                          ival  .=. sem_Lit i .*. EmptyRec
sem_Expr asp (Var v)   = knitAspect var asp$
                          vname .=. sem_Lit v .*. EmptyRec


add_eval  =  syndefM eval add  $ (+) <$> at leftAdd eval <*> at rightAdd eval
val_eval  =  syndefM eval val  $ ter ival


-- asp' =
--  (syndefM eval var (fst <$> ((,) <$> pure (0::Integer) <*> ter vname))) .+:
--       singAsp add_eval .:+: singAsp val_eval

-- asp =
--  singAsp (syndefM eval var (
--              do env <- at lhs env
--                 return env))
--  .:+:
--       singAsp add_eval .:+: singAsp val_eval


aspAll =
  (inhasp leftAdd) --`ext` emptyRule
  .+:
  (inhasp rightAdd
  .+:
     ((syndefM eval var(
              do env <- at lhs env
                 x <- ter vname
                 case lookup x env of
                   Just e -> return e
              )
          )
  .+: (add_eval
  .+: val_eval .+: emptyAspect)))

inhasp chi = inhdefM env add chi (at lhs env)


evalExpr e = sem_Expr aspAll e (env =. [("x",(4 :: Integer)), ("y",99)]
                                *. emptyAtt) #. eval


exampleExpr =  Add (Add (Val (-9)) (Add (Val 7) (Val 2)))
                   (Add (Var "x")(Var "y"))
--exampleEval =  evalExpr exampleExpr


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
