{-# OPTIONS -XMultiParamTypeClasses -XFunctionalDependencies 
            -XFlexibleContexts -XFlexibleInstances 
            -XUndecidableInstances 
            -XExistentialQuantification 
            -XEmptyDataDecls -XRank2Types
            -XTypeSynonymInstances -XTypeOperators -XDataKinds -XTypeFamilies
            -XScopedTypeVariables #-}


import Data.Type.Equality
import AspectAG
import HList
import FakePrelude
import HArray
import HListPrelude
import Record hiding (hUpdateAtLabel)
import GhcSyntax

import Data.Type.Equality

--data types-------------------------------------------------------------------
data Root = Root Tree
          deriving Show

data Tree = Node Tree Tree
          | Leaf Int
          deriving Show


--data types' dependent definitions


----non terminals
nt_Root = label::Label Root
nt_Tree = label::Label Tree

----productions
data P_Root;   p_Root    = label::Label P_Root
data P_Node;   p_Node    = label::Label P_Node
data P_Leaf;   p_Leaf    = label::Label P_Leaf

----children labels
data Ch_tree;   ch_tree  = label::Label (Ch_tree, Tree)
data Ch_l;      ch_l     = label::Label (Ch_l,    Tree)
data Ch_r;      ch_r     = label::Label (Ch_r,    Tree)
data Ch_i;      ch_i     = label::Label (Ch_i,    Int)
data Label1; data Label2; data Label3 ; data LabelL ; data LabelR
data Label4

data Label l = Label
label = Label
label1 = Label :: Label Label1
label2 = Label :: Label Label2
label3 = Label :: Label Label3

--att1 = Attribute 3   :: Attribute Label1 Int 
--att2 = Attribute '4' :: Attribute Label2 Char
att1 = LVPair 3    :: Att Label1 Int
att2 = LVPair '4'  :: Att Label2 Char 
att3 = LVPair True :: Att Label3 Bool
att4 = LVPair True :: Att Label4 Bool
--attrib1 = ConsAtt att2 EmptyAtt
--attrib2 = ConsAtt att1 attrib1

attrib1  = mkRecord $ HCons att2 HNil
attrib2  = att1 .*. attrib1
attrib4  = att4 .*. emptyRecord

-- childAttLR = ConsCh (TaggedChAttr labelL attrib1)$
--             ConsCh (TaggedChAttr labelR attrib2) EmptyCh

tagChi :: Label l -> attrib -> Chi l attrib
tagChi l a = LVPair a

childAttLR = (tagChi (Label:: Label (LabelL,Char) ) attrib1) .*.
             (tagChi (Label:: Label (LabelR,Char) ) attrib2) .*. emptyRecord


pch = tagChi (Label :: Label (LabelR,Char)) True

t = undefined :: HTrue

testsd = singledef t t (undefined::Label3) pch childAttLR



nts = HCons (undefined :: Char) HNil

--testdefs = defs '4' nts 



instance ShowLabel Label1 where
  showLabel _ = "label1"


instance ShowLabel Label2 where
  showLabel _ = "label2"


instance ShowLabel Label3 where
  showLabel _ = "label3"


instance ShowLabel Label4 where
  showLabel _ = "label4"


instance ShowLabel LabelL where
  showLabel _ = "labelL"


instance ShowLabel LabelR where
  showLabel _ = "label1R"

instance (ShowLabel l) => ShowLabel (l,t) where
  showLabel (l :: (l,t)) = (showLabel ::(l -> String)) undefined

instance (HEq' b l m hb, ((l==m) ~ b), HBool hb) => HEq l m hb


class HEq' (d::Bool) l m b | d l m -> b
instance ((l == m) ~ True) => HEq' True l m HTrue
instance ((l == m) ~ False) => HEq' False l m HFalse

