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
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Either
import Language.Grammars.AspectAG.RecordInstances

import Data.GenRec hiding (Label)
import Data.GenRec.Label


type Nt_Expr = 'NT "Expr"
expr = SNT SSym:: Sing Nt_Expr

type P_Add = 'Prd "Add" Nt_Expr
p_Add = SPrd SSym expr :: Sing P_Add

ch_LeftAdd :: Sing ('Chi "LeftAdd" P_Add ('Left Nt_Expr))
ch_LeftAdd = SChi SSym p_Add (SLeft $ SNT SSym)

ch_RightAdd :: Sing ('Chi "RightAdd" P_Add ('Left Nt_Expr))
ch_RightAdd = SChi SSym p_Add (SLeft $ SNT SSym)

type P_Val = 'Prd "Val" Nt_Expr
p_Val = SPrd SSym expr :: Sing P_Val

ch_Val :: Sing ('Chi "iVal"      P_Val ('Right ('T Integer)))
ch_Val = SChi SSym p_Val (SRight $ ST sing)

--------------------------------------------------------------------
type P_Exp1 = 'Prd "Exp1" Nt_Expr
p_Exp1 = SPrd SSym expr :: Sing P_Exp1

ch_Exp1 :: Sing ('Chi "Exp1" P_Exp1 ('Left Nt_Expr))
ch_Exp1 = SChi SSym p_Exp1 (SLeft $ SNT SSym)

asp_Exp1 =
  singAsp $ syn seval p_Exp1
  (flip (^) 1 <$> at ch_Exp1 seval)

--------------------------------------------------------------------
type P_Exp2 = 'Prd "Exp2" Nt_Expr
p_Exp2 = SPrd SSym expr :: Sing P_Exp2

ch_Exp2 :: Sing ('Chi "Exp2" P_Exp2 ('Left Nt_Expr))
ch_Exp2 = SChi SSym p_Exp2 (SLeft $ SNT SSym)

asp_Exp2 =
  singAsp $ syn seval p_Exp2
  (flip (^) 2 <$> at ch_Exp2 seval)

--------------------------------------------------------------------
type P_Exp3 = 'Prd "Exp3" Nt_Expr
p_Exp3 = SPrd SSym expr :: Sing P_Exp3

ch_Exp3 :: Sing ('Chi "Exp3" P_Exp3 ('Left Nt_Expr))
ch_Exp3 = SChi SSym p_Exp3 (SLeft $ SNT SSym)

asp_Exp3 =
  singAsp $ syn seval p_Exp3
  (flip (^) 1 <$> at ch_Exp3 seval)

--------------------------------------------------------------------
type P_Exp4 = 'Prd "Exp4" Nt_Expr
p_Exp4 = SPrd SSym expr :: Sing P_Exp4

ch_Exp4 :: Sing ('Chi "Exp4" P_Exp4 ('Left Nt_Expr))
ch_Exp4 = SChi SSym p_Exp4 (SLeft $ SNT SSym)

asp_Exp4 =
  singAsp $ syn seval p_Exp4
  (flip (^) 4 <$> at ch_Exp4 seval)

--------------------------------------------------------------------
type P_Exp5 = 'Prd "Exp5" Nt_Expr
p_Exp5 = SPrd SSym expr :: Sing P_Exp5

ch_Exp5 :: Sing ('Chi "Exp5" P_Exp5 ('Left Nt_Expr))
ch_Exp5 = SChi SSym p_Exp5 (SLeft $ SNT SSym)

asp_Exp5 =
  singAsp $ syn seval p_Exp5
  (flip (^) 5 <$> at ch_Exp5 seval)
----------------------------------------------------------------------

seval :: Sing ('Att "seval" Integer)
seval = SAtt SSym sing

data Expr = Val Integer
          | Add Expr Expr
          | Exp1 Expr
          | Exp2 Expr
          | Exp3 Expr
          | Exp4 Expr
          | Exp5 Expr
          | Exp01 Expr
          | Exp02 Expr
          | Exp03 Expr
          | Exp04 Expr
          | Exp05 Expr
          | Exp11 Expr
          | Exp12 Expr
          | Exp13 Expr
          | Exp14 Expr
          | Exp15 Expr
          | Exp21 Expr
          | Exp22 Expr
          | Exp23 Expr
          | Exp24 Expr
          | Exp25 Expr
          | Exp31 Expr
          | Exp32 Expr
          | Exp33 Expr
          | Exp34 Expr
          | Exp35 Expr
       deriving Show

sem_Expr asp (Add l r) = knitAspect p_Add asp
                           $  ch_LeftAdd  .=. sem_Expr asp l
                          .*. ch_RightAdd .=. sem_Expr asp r
                          .*.  EmptyRec
sem_Expr asp (Val i)   = knitAspect p_Val asp$
                          ch_Val  .=. sem_Lit i .*. EmptyRec
sem_Expr asp (Exp1 v)   = knitAspect p_Exp1 asp
                          $ ch_Exp1 .=. sem_Expr asp v
                         .*. EmptyRec
-- sem_Expr asp (Exp2 v)   = knitAspect p_Exp2 asp
--                           $ ch_Exp2 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp3 v)   = knitAspect p_Exp3 asp
--                           $ ch_Exp3 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp4 v)   = knitAspect p_Exp4 asp
--                           $ ch_Exp4 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp5 v)   = knitAspect p_Exp5 asp
--                           $ ch_Exp5 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp01 v)   = knitAspect p_Exp01 asp
--                           $ ch_Exp01 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp02 v)   = knitAspect p_Exp02 asp
--                           $ ch_Exp02 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp03 v)   = knitAspect p_Exp03 asp
--                           $ ch_Exp03 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp04 v)   = knitAspect p_Exp04 asp
--                           $ ch_Exp04 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp05 v)   = knitAspect p_Exp05 asp
--                           $ ch_Exp05 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp11 v)   = knitAspect p_Exp11 asp
--                           $ ch_Exp11 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp12 v)   = knitAspect p_Exp12 asp
--                           $ ch_Exp12 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp13 v)   = knitAspect p_Exp13 asp
--                           $ ch_Exp13 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp14 v)   = knitAspect p_Exp14 asp
--                           $ ch_Exp14 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp15 v)   = knitAspect p_Exp15 asp
--                           $ ch_Exp15 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp21 v)   = knitAspect p_Exp21 asp
--                           $ ch_Exp21 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp22 v)   = knitAspect p_Exp22 asp
--                           $ ch_Exp22 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp23 v)   = knitAspect p_Exp23 asp
--                           $ ch_Exp23 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp24 v)   = knitAspect p_Exp24 asp
--                           $ ch_Exp24 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp25 v)   = knitAspect p_Exp25 asp
--                           $ ch_Exp25 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp31 v)   = knitAspect p_Exp31 asp
--                           $ ch_Exp31 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp32 v)   = knitAspect p_Exp32 asp
--                           $ ch_Exp32 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp33 v)   = knitAspect p_Exp33 asp
--                           $ ch_Exp33 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp34 v)   = knitAspect p_Exp34 asp
--                           $ ch_Exp34 .=. sem_Expr asp v
--                          .*. EmptyRec
-- sem_Expr asp (Exp35 v)   = knitAspect p_Exp35 asp
--                           $ ch_Exp35 .=. sem_Expr asp v
--                          .*. EmptyRec
                         
asp_Add =
  singAsp $ syn seval p_Add
  ( (+) <$> at ch_LeftAdd seval <*> at ch_RightAdd seval)

asp_Val =
  singAsp $ syn seval p_Val $ ter ch_Val

asp_All = asp_Val .:+: asp_Add
  .:+: asp_Exp1
  -- .:+: asp_Exp2
  -- .:+: asp_Exp3
  -- .:+: asp_Exp4
  -- .:+: asp_Exp5
  -- .:+: asp_Exp01
  -- .:+: asp_Exp02
  -- .:+: asp_Exp03
  -- .:+: asp_Exp04
  -- .:+: asp_Exp05
  -- .:+: asp_Exp11
  -- .:+: asp_Exp12
  -- .:+: asp_Exp13
  -- .:+: asp_Exp14
  -- .:+: asp_Exp15
  -- .:+: asp_Exp21
  -- .:+: asp_Exp22
  -- .:+: asp_Exp23
  -- .:+: asp_Exp24
  -- .:+: asp_Exp25
  -- .:+: asp_Exp31
  -- .:+: asp_Exp32
  -- .:+: asp_Exp33
  -- .:+: asp_Exp34
  -- .:+: asp_Exp35

exampleT = Exp1 ((Val 2) `Add` (Val 3))

eval e = sem_Expr asp_All e emptyAtt #. seval



--------------------------------------------------------------------
type P_Exp01 = 'Prd "Exp01" Nt_Expr
p_Exp01 = SPrd SSym expr :: Sing P_Exp01

ch_Exp01 :: Sing ('Chi "Exp01" P_Exp01 ('Left Nt_Expr))
ch_Exp01 = SChi SSym p_Exp01 (SLeft $ SNT SSym)

asp_Exp01 =
  singAsp $ syn seval p_Exp01
  (flip (^) 1 <$> at ch_Exp01 seval)

--------------------------------------------------------------------
type P_Exp02 = 'Prd "Exp02" Nt_Expr
p_Exp02 = SPrd SSym expr :: Sing P_Exp02

ch_Exp02 :: Sing ('Chi "Exp02" P_Exp02 ('Left Nt_Expr))
ch_Exp02 = SChi SSym p_Exp02 (SLeft $ SNT SSym)

asp_Exp02 =
  singAsp $ syn seval p_Exp02
  (flip (^) 2 <$> at ch_Exp02 seval)

--------------------------------------------------------------------
type P_Exp03 = 'Prd "Exp03" Nt_Expr
p_Exp03 = SPrd SSym expr :: Sing P_Exp03

ch_Exp03 :: Sing ('Chi "Exp03" P_Exp03 ('Left Nt_Expr))
ch_Exp03 = SChi SSym p_Exp03 (SLeft $ SNT SSym)

asp_Exp03 =
  singAsp $ syn seval p_Exp03
  (flip (^) 1 <$> at ch_Exp03 seval)

--------------------------------------------------------------------
type P_Exp04 = 'Prd "Exp04" Nt_Expr
p_Exp04 = SPrd SSym expr :: Sing P_Exp04

ch_Exp04 :: Sing ('Chi "Exp04" P_Exp04 ('Left Nt_Expr))
ch_Exp04 = SChi SSym p_Exp04 (SLeft $ SNT SSym)

asp_Exp04 =
  singAsp $ syn seval p_Exp04
  (flip (^) 4 <$> at ch_Exp04 seval)

--------------------------------------------------------------------
type P_Exp05 = 'Prd "Exp05" Nt_Expr
p_Exp05 = SPrd SSym expr :: Sing P_Exp05

ch_Exp05 :: Sing ('Chi "Exp05" P_Exp05 ('Left Nt_Expr))
ch_Exp05 = SChi SSym p_Exp05 (SLeft $ SNT SSym)

asp_Exp05 =
  singAsp $ syn seval p_Exp05
  (flip (^) 5 <$> at ch_Exp05 seval)
----------------------------------------------------------------------


--------------------------------------------------------------------
type P_Exp11 = 'Prd "Exp11" Nt_Expr
p_Exp11 = SPrd SSym expr :: Sing P_Exp11

ch_Exp11 :: Sing ('Chi "Exp11" P_Exp11 ('Left Nt_Expr))
ch_Exp11 = SChi SSym p_Exp11 (SLeft $ SNT SSym)

asp_Exp11 =
  singAsp $ syn seval p_Exp11
  (flip (^) 1 <$> at ch_Exp11 seval)

--------------------------------------------------------------------
type P_Exp12 = 'Prd "Exp12" Nt_Expr
p_Exp12 = SPrd SSym expr :: Sing P_Exp12

ch_Exp12 :: Sing ('Chi "Exp12" P_Exp12 ('Left Nt_Expr))
ch_Exp12 = SChi SSym p_Exp12 (SLeft $ SNT SSym)

asp_Exp12 =
  singAsp $ syn seval p_Exp12
  (flip (^) 2 <$> at ch_Exp12 seval)

--------------------------------------------------------------------
type P_Exp13 = 'Prd "Exp13" Nt_Expr
p_Exp13 = SPrd SSym expr :: Sing P_Exp13

ch_Exp13 :: Sing ('Chi "Exp13" P_Exp13 ('Left Nt_Expr))
ch_Exp13 = SChi SSym p_Exp13 (SLeft $ SNT SSym)

asp_Exp13 =
  singAsp $ syn seval p_Exp13
  (flip (^) 1 <$> at ch_Exp13 seval)

--------------------------------------------------------------------
type P_Exp14 = 'Prd "Exp14" Nt_Expr
p_Exp14 = SPrd SSym expr :: Sing P_Exp14

ch_Exp14 :: Sing ('Chi "Exp14" P_Exp14 ('Left Nt_Expr))
ch_Exp14 = SChi SSym p_Exp14 (SLeft $ SNT SSym)

asp_Exp14 =
  singAsp $ syn seval p_Exp14
  (flip (^) 4 <$> at ch_Exp14 seval)

--------------------------------------------------------------------
type P_Exp15 = 'Prd "Exp15" Nt_Expr
p_Exp15 = SPrd SSym expr :: Sing P_Exp15

ch_Exp15 :: Sing ('Chi "Exp15" P_Exp15 ('Left Nt_Expr))
ch_Exp15 = SChi SSym p_Exp15 (SLeft $ SNT SSym)

asp_Exp15 =
  singAsp $ syn seval p_Exp15
  (flip (^) 5 <$> at ch_Exp15 seval)
----------------------------------------------------------------------

--------------------------------------------------------------------
type P_Exp21 = 'Prd "Exp21" Nt_Expr
p_Exp21 = SPrd SSym expr :: Sing P_Exp21

ch_Exp21 :: Sing ('Chi "Exp21" P_Exp21 ('Left Nt_Expr))
ch_Exp21 = SChi SSym p_Exp21 (SLeft $ SNT SSym)

asp_Exp21 =
  singAsp $ syn seval p_Exp21
  (flip (^) 1 <$> at ch_Exp21 seval)

--------------------------------------------------------------------
type P_Exp22 = 'Prd "Exp22" Nt_Expr
p_Exp22 = SPrd SSym expr :: Sing P_Exp22

ch_Exp22 :: Sing ('Chi "Exp22" P_Exp22 ('Left Nt_Expr))
ch_Exp22 = SChi SSym p_Exp22 (SLeft $ SNT SSym)

asp_Exp22 =
  singAsp $ syn seval p_Exp22
  (flip (^) 2 <$> at ch_Exp22 seval)

--------------------------------------------------------------------
type P_Exp23 = 'Prd "Exp23" Nt_Expr
p_Exp23 = SPrd SSym expr :: Sing P_Exp23

ch_Exp23 :: Sing ('Chi "Exp23" P_Exp23 ('Left Nt_Expr))
ch_Exp23 = SChi SSym p_Exp23 (SLeft $ SNT SSym)

asp_Exp23 =
  singAsp $ syn seval p_Exp23
  (flip (^) 1 <$> at ch_Exp23 seval)

--------------------------------------------------------------------
type P_Exp24 = 'Prd "Exp24" Nt_Expr
p_Exp24 = SPrd SSym expr :: Sing P_Exp24

ch_Exp24 :: Sing ('Chi "Exp24" P_Exp24 ('Left Nt_Expr))
ch_Exp24 = SChi SSym p_Exp24 (SLeft $ SNT SSym)

asp_Exp24 =
  singAsp $ syn seval p_Exp24
  (flip (^) 4 <$> at ch_Exp24 seval)

--------------------------------------------------------------------
type P_Exp25 = 'Prd "Exp25" Nt_Expr
p_Exp25 = SPrd SSym expr :: Sing P_Exp25

ch_Exp25 :: Sing ('Chi "Exp25" P_Exp25 ('Left Nt_Expr))
ch_Exp25 = SChi SSym p_Exp25 (SLeft $ SNT SSym)

asp_Exp25 =
  singAsp $ syn seval p_Exp25
  (flip (^) 5 <$> at ch_Exp25 seval)
----------------------------------------------------------------------



--------------------------------------------------------------------
type P_Exp31 = 'Prd "Exp31" Nt_Expr
p_Exp31 = SPrd SSym expr :: Sing P_Exp31

ch_Exp31 :: Sing ('Chi "Exp31" P_Exp31 ('Left Nt_Expr))
ch_Exp31 = SChi SSym p_Exp31 (SLeft $ SNT SSym)

asp_Exp31 =
  singAsp $ syn seval p_Exp31
  (flip (^) 1 <$> at ch_Exp31 seval)

--------------------------------------------------------------------
type P_Exp32 = 'Prd "Exp32" Nt_Expr
p_Exp32 = SPrd SSym expr :: Sing P_Exp32

ch_Exp32 :: Sing ('Chi "Exp32" P_Exp32 ('Left Nt_Expr))
ch_Exp32 = SChi SSym p_Exp32 (SLeft $ SNT SSym)

asp_Exp32 =
  singAsp $ syn seval p_Exp32
  (flip (^) 2 <$> at ch_Exp32 seval)

--------------------------------------------------------------------
type P_Exp33 = 'Prd "Exp33" Nt_Expr
p_Exp33 = SPrd SSym expr :: Sing P_Exp33

ch_Exp33 :: Sing ('Chi "Exp33" P_Exp33 ('Left Nt_Expr))
ch_Exp33 = SChi SSym p_Exp33 (SLeft $ SNT SSym)

asp_Exp33 =
  singAsp $ syn seval p_Exp33
  (flip (^) 1 <$> at ch_Exp33 seval)

--------------------------------------------------------------------
type P_Exp34 = 'Prd "Exp34" Nt_Expr
p_Exp34 = SPrd SSym expr :: Sing P_Exp34

ch_Exp34 :: Sing ('Chi "Exp34" P_Exp34 ('Left Nt_Expr))
ch_Exp34 = SChi SSym p_Exp34 (SLeft $ SNT SSym)

asp_Exp34 =
  singAsp $ syn seval p_Exp34
  (flip (^) 4 <$> at ch_Exp34 seval)

--------------------------------------------------------------------
type P_Exp35 = 'Prd "Exp35" Nt_Expr
p_Exp35 = SPrd SSym expr :: Sing P_Exp35

ch_Exp35 :: Sing ('Chi "Exp35" P_Exp35 ('Left Nt_Expr))
ch_Exp35 = SChi SSym p_Exp35 (SLeft $ SNT SSym)

asp_Exp35 =
  singAsp $ syn seval p_Exp35
  (flip (^) 5 <$> at ch_Exp35 seval)
----------------------------------------------------------------------

l :: GFam P_Add NonExtensible Bool Bool
l = undefined




-----------------------aca termina el ejemplo original------------------
