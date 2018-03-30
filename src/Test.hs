{-# LANGUAGE TypeInType,
             GADTs,
             KindSignatures,
             TypeOperators,
             TypeFamilies,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             StandaloneDeriving,
             UndecidableInstances,
             FunctionalDependencies,
             ConstraintKinds,
             ScopedTypeVariables,
             AllowAmbiguousTypes,
             UnicodeSyntax#-}

module Test where

import HList
import Attribution
import Record
import Attribute
import Data.Kind
import Data.Tagged
import TPrelude
import AspectAG




data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving Show

--emptyRule ∷ Rule '[] '[] '[] '[] '[] '[]
--emptyRule = \r -> id

-- Labels (attribute names) for the example
data Att_smin
data Att_ival
data Att_sres

-- Labels for childs
data Ch_tree -- root
data Ch_r    -- node
data Ch_l    -- node
data Ch_i    -- leaf

smin = Label :: Label Att_smin
ival = Label :: Label Att_ival
sres = Label :: Label Att_sres

ch_tree = Label :: Label (Ch_tree, Tree)
ch_r = Label :: Label (Ch_r, Tree)
ch_l = Label :: Label (Ch_l, Tree)
ch_i = Label :: Label (Ch_i, Int)


type SP = '[ '(Att_smin,Int), '(Att_sres, Tree)]
type IL = '[ '(Att_ival, Int)]
type IR = '[ '(Att_ival, Int)]

type IC = '[ '((Ch_l,Tree),Attribution IL), '((Ch_r, Tree),Attribution IR)]

type Output_Node_Fam = Fam IC SP

testFam = Fam record attributionP -- :: Output_Node_Fam

attributionP = (smin .=. 3) .*. (sres .=. Leaf 4) .*. EmptyAtt
attributionL = (ival .=. 2) .*. EmptyAtt
attributionR = (ival .=. 6) .*. EmptyAtt
record = (ch_l =. attributionL ) *. (ch_r =. attributionR) *. EmptyR


test_syndef_1 = syndef ival "string" testFam

test_synmod_1 = synmod smin "er" testFam
