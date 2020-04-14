{-# LANGUAGE TypeFamilies #-}
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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}

module Language.Grammars.AspectAG.GenRecordTest where

import Data.Kind
import Data.Proxy
import Language.Grammars.AspectAG.GenRecord
import Language.Grammars.AspectAG.Label


import GHC.TypeLits

tst_emp = EmptyRec

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

tagField :: Label l -> v -> TagField Reco l v
tagField l v = TagField Label Label v

handmade =
    ConsRec (tagField label1 True)
  $ ConsRec (tagField label2 "lolo")
  $ ConsRec (tagField label4 (3::Int))
  EmptyRec

true  = handmade # label1
-- boom  = handmade # label3 -- should have a nice error message
-- boom2 = handmade # label5 -- should have a nice error message

anInt = handmade # label4
