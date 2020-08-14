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

import Data.Singletons.Prelude.Ord


import Data.GenRec hiding (Label)
import Data.GenRec.Label
import Data.Kind

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
  ( do l <- at ch_LeftAdd seval
       r <- at ch_RightAdd seval
       return (l+r))

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

exampleT = Exp1 $ (Val 2) `Add` (Val 3)

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

-----------------------aca termina el ejemplo original------------------

type Fam_Add c p = GFam P_Add 'NonExtensible c p
type Fam_Val c p = GFam P_Val 'NonExtensible c p


data instance GFam P_Add 'NonExtensible
  ('(l,r) :: ([(Att, Type)], [(Att, Type)]))
  (p :: [(Att, Type)]) where
  Fam_Add
    :: (Attribution l, Attribution r)
    -> Attribution p
    -> Fam_Add '(l, r) p 

data instance GFam P_Val 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Val
    :: Attribution c
    -> Attribution p
    -> Fam_Val c p

-- homebrew rules
-- add_rule :: Fam_Add P_Add 'NonExtensible sc ip
--          -> Fam_Add P_Add 'NonExtensible ic sp
--          -> Fam_Add P_Add 'NonExtensible ic (Extend AttReco)
add_rule = singAsp $ CGRule p_Add $
           \(Fam_Add (lsc,rsc) ip) (Fam_Add ic@(lic,ric) sp) ->
             Fam_Add ic (seval .=. (lsc #. seval) + (rsc #. seval) .*.  sp)

val_rule = singAsp $ CGRule p_Val
  $ \(Fam_Val sc ip)
     (Fam_Val ic sp) ->
      Fam_Val ic (seval .=. (sc #. (lit @ Integer)) .*. sp)

rule_Exp1 = singAsp $ CGRule p_Exp1
  $ \(Fam_Exp1 sc ip)
     (Fam_Exp1 ic sp) ->
      Fam_Exp1 ic (seval .=. (sc #. seval ) .*. sp)

knit_Add (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = (emptyAtt, emptyAtt)
      (Fam_Add (lic,ric) sp) = rule (Fam_Add sc ip)(Fam_Add ec emptyAtt)
      sc = ((fst fc) lic, (snd fc) ric) 
  in sp

knit_Exp1 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp1 ic sp) = rule (Fam_Exp1 sc ip)(Fam_Exp1 ec emptyAtt)
      sc = fc ic 
  in sp

knit_Val (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Val ic sp) = rule (Fam_Val sc ip)(Fam_Val ec emptyAtt)
      sc = fc ic
  in sp

sem (asp ::Aspect a) (Add l r) = knit_Add (asp # p_Add)
                                 (sem asp l,sem asp r)
sem (asp ::Aspect a) (Val i)   = knit_Val (asp # p_Val) (sem_Lit i)
sem (asp ::Aspect a) (Exp1 e)  = knit_Exp1 (asp # p_Exp1) (sem asp e)
sem (asp ::Aspect a) (Exp2 e)  = knit_Exp2 (asp # p_Exp2) (sem asp e)
sem (asp ::Aspect a) (Exp3 e)  = knit_Exp3 (asp # p_Exp3) (sem asp e)
sem (asp ::Aspect a) (Exp4 e)  = knit_Exp4 (asp # p_Exp4) (sem asp e)
sem (asp ::Aspect a) (Exp5 e)  = knit_Exp5 (asp # p_Exp5) (sem asp e)
sem (asp ::Aspect a) (Exp01 e)  = knit_Exp01 (asp # p_Exp01) (sem asp e)
sem (asp ::Aspect a) (Exp02 e)  = knit_Exp02 (asp # p_Exp02) (sem asp e)
sem (asp ::Aspect a) (Exp03 e)  = knit_Exp03 (asp # p_Exp03) (sem asp e)
sem (asp ::Aspect a) (Exp04 e)  = knit_Exp04 (asp # p_Exp04) (sem asp e)
sem (asp ::Aspect a) (Exp05 e)  = knit_Exp05 (asp # p_Exp05) (sem asp e)
sem (asp ::Aspect a) (Exp11 e)  = knit_Exp11 (asp # p_Exp11) (sem asp e)
sem (asp ::Aspect a) (Exp12 e)  = knit_Exp12 (asp # p_Exp12) (sem asp e)
sem (asp ::Aspect a) (Exp13 e)  = knit_Exp13 (asp # p_Exp13) (sem asp e)
sem (asp ::Aspect a) (Exp14 e)  = knit_Exp14 (asp # p_Exp14) (sem asp e)
sem (asp ::Aspect a) (Exp15 e)  = knit_Exp15 (asp # p_Exp15) (sem asp e)
sem (asp ::Aspect a) (Exp21 e)  = knit_Exp21 (asp # p_Exp21) (sem asp e)
sem (asp ::Aspect a) (Exp22 e)  = knit_Exp22 (asp # p_Exp22) (sem asp e)
sem (asp ::Aspect a) (Exp23 e)  = knit_Exp23 (asp # p_Exp23) (sem asp e)
sem (asp ::Aspect a) (Exp24 e)  = knit_Exp24 (asp # p_Exp24) (sem asp e)
sem (asp ::Aspect a) (Exp25 e)  = knit_Exp25 (asp # p_Exp25) (sem asp e)
sem (asp ::Aspect a) (Exp31 e)  = knit_Exp31 (asp # p_Exp31) (sem asp e)
sem (asp ::Aspect a) (Exp32 e)  = knit_Exp32 (asp # p_Exp32) (sem asp e)
sem (asp ::Aspect a) (Exp33 e)  = knit_Exp33 (asp # p_Exp33) (sem asp e)
sem (asp ::Aspect a) (Exp34 e)  = knit_Exp34 (asp # p_Exp34) (sem asp e)
sem (asp ::Aspect a) (Exp35 e)  = knit_Exp35 (asp # p_Exp35) (sem asp e)

eval' e = sem aspall e emptyAtt #. seval

aspall = add_rule .:+: val_rule .:+:
  rule_Exp1 .:+: rule_Exp2 .:+: rule_Exp3 .:+: rule_Exp4 .:+: rule_Exp5 .:+:
  rule_Exp01 .:+: rule_Exp02 .:+: rule_Exp03 .:+: rule_Exp04 .:+: rule_Exp05 .:+:
  rule_Exp11 .:+: rule_Exp12 .:+: rule_Exp13 .:+: rule_Exp14 .:+: rule_Exp15 .:+:
  rule_Exp21 .:+: rule_Exp22 .:+: rule_Exp23 .:+: rule_Exp24 .:+: rule_Exp25 .:+:
  rule_Exp31 .:+: rule_Exp32 .:+: rule_Exp33 .:+: rule_Exp34 .:+: rule_Exp35 .:+:
  emptyAspect



type instance GRule P_Val NonExtensible
  (sc   :: [(Att, Type)])
  (ip   :: [(Att, Type)])
  (ic   :: [(Att, Type)])
  (sp   :: [(Att, Type)])
  (ic'   :: [(Att, Type)])
  (sp'   :: [(Att, Type)])
  = GFam P_Val NonExtensible sc ip
  -> GFam P_Val NonExtensible ic sp
  -> GFam P_Val NonExtensible ic' sp'

type instance GRule P_Val NonExtensible
  (sc   :: ([(Att, Type)], [(Att, Type)]))
  (ip   :: [(Att, Type)])
  (ic   :: ([(Att, Type)], [(Att, Type)]))
  (sp   :: [(Att, Type)])
  (ic'  :: ([(Att, Type)], [(Att, Type)]))
  (sp'  :: [(Att, Type)])
  = GFam P_Val NonExtensible sc ip
  -> GFam P_Val NonExtensible ic sp
  -> GFam P_Val NonExtensible ic' sp'


type Fam_Exp1 c p = GFam P_Exp1 'NonExtensible c p
data instance GFam P_Exp1 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp1
    :: Attribution c
    -> Attribution p
    -> Fam_Exp1 c p
    
type Fam_Exp2 c p = GFam P_Exp2 'NonExtensible c p
data instance GFam P_Exp2 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp2
    :: Attribution c
    -> Attribution p
    -> Fam_Exp2 c p 

type Fam_Exp3 c p = GFam P_Exp3 'NonExtensible c p
data instance GFam P_Exp3 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp3
    :: Attribution c
    -> Attribution p
    -> Fam_Exp3 c p 

type Fam_Exp4 c p = GFam P_Exp4 'NonExtensible c p
data instance GFam P_Exp4 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp4
    :: Attribution c
    -> Attribution p
    -> Fam_Exp4 c p 

type Fam_Exp5 c p = GFam P_Exp5 'NonExtensible c p
data instance GFam P_Exp5 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp5
    :: Attribution c
    -> Attribution p
    -> Fam_Exp5 c p 


type Fam_Exp01 c p = GFam P_Exp01 'NonExtensible c p
data instance GFam P_Exp01 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp01
    :: Attribution c
    -> Attribution p
    -> Fam_Exp01 c p
    
type Fam_Exp02 c p = GFam P_Exp02 'NonExtensible c p
data instance GFam P_Exp02 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp02
    :: Attribution c
    -> Attribution p
    -> Fam_Exp02 c p 

type Fam_Exp03 c p = GFam P_Exp03 'NonExtensible c p
data instance GFam P_Exp03 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp03
    :: Attribution c
    -> Attribution p
    -> Fam_Exp03 c p 

type Fam_Exp04 c p = GFam P_Exp04 'NonExtensible c p
data instance GFam P_Exp04 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp04
    :: Attribution c
    -> Attribution p
    -> Fam_Exp04 c p 

type Fam_Exp05 c p = GFam P_Exp05 'NonExtensible c p
data instance GFam P_Exp05 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp05
    :: Attribution c
    -> Attribution p
    -> Fam_Exp05 c p 


type Fam_Exp11 c p = GFam P_Exp11 'NonExtensible c p
data instance GFam P_Exp11 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp11
    :: Attribution c
    -> Attribution p
    -> Fam_Exp11 c p
    
type Fam_Exp12 c p = GFam P_Exp12 'NonExtensible c p
data instance GFam P_Exp12 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp12
    :: Attribution c
    -> Attribution p
    -> Fam_Exp12 c p 

type Fam_Exp13 c p = GFam P_Exp13 'NonExtensible c p
data instance GFam P_Exp13 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp13
    :: Attribution c
    -> Attribution p
    -> Fam_Exp13 c p 

type Fam_Exp14 c p = GFam P_Exp14 'NonExtensible c p
data instance GFam P_Exp14 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp14
    :: Attribution c
    -> Attribution p
    -> Fam_Exp14 c p 

type Fam_Exp15 c p = GFam P_Exp15 'NonExtensible c p
data instance GFam P_Exp15 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp15
    :: Attribution c
    -> Attribution p
    -> Fam_Exp15 c p 

type Fam_Exp21 c p = GFam P_Exp21 'NonExtensible c p
data instance GFam P_Exp21 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp21
    :: Attribution c
    -> Attribution p
    -> Fam_Exp21 c p
    
type Fam_Exp22 c p = GFam P_Exp22 'NonExtensible c p
data instance GFam P_Exp22 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp22
    :: Attribution c
    -> Attribution p
    -> Fam_Exp22 c p 

type Fam_Exp23 c p = GFam P_Exp23 'NonExtensible c p
data instance GFam P_Exp23 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp23
    :: Attribution c
    -> Attribution p
    -> Fam_Exp23 c p 

type Fam_Exp24 c p = GFam P_Exp24 'NonExtensible c p
data instance GFam P_Exp24 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp24
    :: Attribution c
    -> Attribution p
    -> Fam_Exp24 c p 

type Fam_Exp25 c p = GFam P_Exp25 'NonExtensible c p
data instance GFam P_Exp25 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp25
    :: Attribution c
    -> Attribution p
    -> Fam_Exp25 c p 

type Fam_Exp31 c p = GFam P_Exp31 'NonExtensible c p
data instance GFam P_Exp31 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp31
    :: Attribution c
    -> Attribution p
    -> Fam_Exp31 c p
    
type Fam_Exp32 c p = GFam P_Exp32 'NonExtensible c p
data instance GFam P_Exp32 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp32
    :: Attribution c
    -> Attribution p
    -> Fam_Exp32 c p 

type Fam_Exp33 c p = GFam P_Exp33 'NonExtensible c p
data instance GFam P_Exp33 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp33
    :: Attribution c
    -> Attribution p
    -> Fam_Exp33 c p 

type Fam_Exp34 c p = GFam P_Exp34 'NonExtensible c p
data instance GFam P_Exp34 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp34
    :: Attribution c
    -> Attribution p
    -> Fam_Exp34 c p 

type Fam_Exp35 c p = GFam P_Exp35 'NonExtensible c p
data instance GFam P_Exp35 'NonExtensible
  (c :: [(Att, Type)])
  (p :: [(Att, Type)]) where
  Fam_Exp35
    :: Attribution c
    -> Attribution p
    -> Fam_Exp35 c p 


knit_Exp2 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp2 ic sp) = rule (Fam_Exp2 sc ip)(Fam_Exp2 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp3 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp3 ic sp) = rule (Fam_Exp3 sc ip)(Fam_Exp3 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp4 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp4 ic sp) = rule (Fam_Exp4 sc ip)(Fam_Exp4 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp5 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp5 ic sp) = rule (Fam_Exp5 sc ip)(Fam_Exp5 ec emptyAtt)
      sc = fc ic 
  in sp

knit_Exp01 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp01 ic sp) = rule (Fam_Exp01 sc ip)(Fam_Exp01 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp02 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp02 ic sp) = rule (Fam_Exp02 sc ip)(Fam_Exp02 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp03 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp03 ic sp) = rule (Fam_Exp03 sc ip)(Fam_Exp03 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp04 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp04 ic sp) = rule (Fam_Exp04 sc ip)(Fam_Exp04 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp05 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp05 ic sp) = rule (Fam_Exp05 sc ip)(Fam_Exp05 ec emptyAtt)
      sc = fc ic 
  in sp



knit_Exp11 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp11 ic sp) = rule (Fam_Exp11 sc ip)(Fam_Exp11 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp12 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp12 ic sp) = rule (Fam_Exp12 sc ip)(Fam_Exp12 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp13 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp13 ic sp) = rule (Fam_Exp13 sc ip)(Fam_Exp13 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp14 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp14 ic sp) = rule (Fam_Exp14 sc ip)(Fam_Exp14 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp15 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp15 ic sp) = rule (Fam_Exp15 sc ip)(Fam_Exp15 ec emptyAtt)
      sc = fc ic 
  in sp



knit_Exp21 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp21 ic sp) = rule (Fam_Exp21 sc ip)(Fam_Exp21 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp22 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp22 ic sp) = rule (Fam_Exp22 sc ip)(Fam_Exp22 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp23 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp23 ic sp) = rule (Fam_Exp23 sc ip)(Fam_Exp23 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp24 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp24 ic sp) = rule (Fam_Exp24 sc ip)(Fam_Exp24 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp25 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp25 ic sp) = rule (Fam_Exp25 sc ip)(Fam_Exp25 ec emptyAtt)
      sc = fc ic 
  in sp



knit_Exp31 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp31 ic sp) = rule (Fam_Exp31 sc ip)(Fam_Exp31 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp32 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp32 ic sp) = rule (Fam_Exp32 sc ip)(Fam_Exp32 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp33 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp33 ic sp) = rule (Fam_Exp33 sc ip)(Fam_Exp33 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp34 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp34 ic sp) = rule (Fam_Exp34 sc ip)(Fam_Exp34 ec emptyAtt)
      sc = fc ic 
  in sp
knit_Exp35 (CGRule p rule)
         fc
         (ip   :: Attribution ip) =
  let ec = emptyAtt
      (Fam_Exp35 ic sp) = rule (Fam_Exp35 sc ip)(Fam_Exp35 ec emptyAtt)
      sc = fc ic 
  in sp


rule_Exp2 = singAsp $ CGRule p_Exp2
  $ \(Fam_Exp2 sc ip)
     (Fam_Exp2 ic sp) ->
      Fam_Exp2 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp3 = singAsp $ CGRule p_Exp3
  $ \(Fam_Exp3 sc ip)
     (Fam_Exp3 ic sp) ->
      Fam_Exp3 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp4 = singAsp $ CGRule p_Exp4
  $ \(Fam_Exp4 sc ip)
     (Fam_Exp4 ic sp) ->
      Fam_Exp4 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp5 = singAsp $ CGRule p_Exp5
  $ \(Fam_Exp5 sc ip)
     (Fam_Exp5 ic sp) ->
      Fam_Exp5 ic (seval .=. (sc #. seval ) .*. sp)

rule_Exp01 = singAsp $ CGRule p_Exp01
  $ \(Fam_Exp01 sc ip)
     (Fam_Exp01 ic sp) ->
      Fam_Exp01 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp02 = singAsp $ CGRule p_Exp02
  $ \(Fam_Exp02 sc ip)
     (Fam_Exp02 ic sp) ->
      Fam_Exp02 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp03 = singAsp $ CGRule p_Exp03
  $ \(Fam_Exp03 sc ip)
     (Fam_Exp03 ic sp) ->
      Fam_Exp03 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp04 = singAsp $ CGRule p_Exp04
  $ \(Fam_Exp04 sc ip)
     (Fam_Exp04 ic sp) ->
      Fam_Exp04 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp05 = singAsp $ CGRule p_Exp05
  $ \(Fam_Exp05 sc ip)
     (Fam_Exp05 ic sp) ->
      Fam_Exp05 ic (seval .=. (sc #. seval ) .*. sp)

rule_Exp11 = singAsp $ CGRule p_Exp11
  $ \(Fam_Exp11 sc ip)
     (Fam_Exp11 ic sp) ->
      Fam_Exp11 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp12 = singAsp $ CGRule p_Exp12
  $ \(Fam_Exp12 sc ip)
     (Fam_Exp12 ic sp) ->
      Fam_Exp12 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp13 = singAsp $ CGRule p_Exp13
  $ \(Fam_Exp13 sc ip)
     (Fam_Exp13 ic sp) ->
      Fam_Exp13 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp14 = singAsp $ CGRule p_Exp14
  $ \(Fam_Exp14 sc ip)
     (Fam_Exp14 ic sp) ->
      Fam_Exp14 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp15 = singAsp $ CGRule p_Exp15
  $ \(Fam_Exp15 sc ip)
     (Fam_Exp15 ic sp) ->
      Fam_Exp15 ic (seval .=. (sc #. seval ) .*. sp)

rule_Exp21 = singAsp $ CGRule p_Exp21
  $ \(Fam_Exp21 sc ip)
     (Fam_Exp21 ic sp) ->
      Fam_Exp21 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp22 = singAsp $ CGRule p_Exp22
  $ \(Fam_Exp22 sc ip)
     (Fam_Exp22 ic sp) ->
      Fam_Exp22 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp23 = singAsp $ CGRule p_Exp23
  $ \(Fam_Exp23 sc ip)
     (Fam_Exp23 ic sp) ->
      Fam_Exp23 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp24 = singAsp $ CGRule p_Exp24
  $ \(Fam_Exp24 sc ip)
     (Fam_Exp24 ic sp) ->
      Fam_Exp24 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp25 = singAsp $ CGRule p_Exp25
  $ \(Fam_Exp25 sc ip)
     (Fam_Exp25 ic sp) ->
      Fam_Exp25 ic (seval .=. (sc #. seval ) .*. sp)


rule_Exp31 = singAsp $ CGRule p_Exp31
  $ \(Fam_Exp31 sc ip)
     (Fam_Exp31 ic sp) ->
      Fam_Exp31 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp32 = singAsp $ CGRule p_Exp32
  $ \(Fam_Exp32 sc ip)
     (Fam_Exp32 ic sp) ->
      Fam_Exp32 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp33 = singAsp $ CGRule p_Exp33
  $ \(Fam_Exp33 sc ip)
     (Fam_Exp33 ic sp) ->
      Fam_Exp33 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp34 = singAsp $ CGRule p_Exp34
  $ \(Fam_Exp34 sc ip)
     (Fam_Exp34 ic sp) ->
      Fam_Exp34 ic (seval .=. (sc #. seval ) .*. sp)
rule_Exp35 = singAsp $ CGRule p_Exp35
  $ \(Fam_Exp35 sc ip)
     (Fam_Exp35 ic sp) ->
      Fam_Exp35 ic (seval .=. (sc #. seval ) .*. sp)
