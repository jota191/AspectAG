{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-|
Module      : Language.Grammars.AspectAG.GenRecord
Description : Record library, this will be eventually forked out
              from AAG codebase and used as a standalone library, depending on it
Copyright   : (c) Juan García Garland, Marcos Viera, 2019
License     : GPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Grammars.AspectAG.GenRecordTest where

import Data.Kind
import Data.Proxy
import Language.Grammars.AspectAG.GenRecord
import Language.Grammars.AspectAG.Label


import GHC.TypeLits

emp = EmptyRec :: Record '[]

label1 = Label @ "l1"
label2 = Label @ "l2"
label3 = Label @ "l3"
label4 = Label @ "l4"
label5 = Label @ "l5"

-- let us define simple records:

data Reco
type instance WrapField Reco v = v
type instance ShowRec Reco = "Record"
type instance ShowField Reco = "field named:"

type Record (r :: [(Symbol, Type)]) = Rec Reco r

tagField :: Label l -> v -> TagField Reco l v
tagField l v = TagField Label Label v

reco = -- "handmade" record, note labels in order
    ConsRec (tagField label1 True)
  $ ConsRec (tagField label2 "lolo")
  $ ConsRec (tagField label4 (3::Int))
    EmptyRec


-- lookup tests

true  = reco # label1
-- boom  = reco # label3 -- should have a nice error message
-- boom2 = reco # label5 -- should have a nice error message
anInt = reco # label4

-- update tests
t1 = update label2 'a' reco
t2 = update label4 'a' reco
--t3 = update label5 True reco
--t4 = update label3 True reco


-- extend
-- e1 = tagField label1 () .*. reco
e2 = tagField label3 () .*. reco
-- e3 = tagField label4 () .*. reco


instance Show (Record '[]) where
  show _ = "{}"
instance (Show (Record r), Show v, KnownSymbol l)
  => Show (Record ( '(l, v) ': r )) where
  show (ConsRec (TagField _ l v) r) =
    let ('{':shr) = show r
    in '{' : symbolVal l ++ " ↦ " ++ show v ++ ", " ++ shr
