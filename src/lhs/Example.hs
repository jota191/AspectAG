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
             UnicodeSyntax#-}

module Example where

import AspectAG
import HList
import Data.Kind

--datatype

data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving Show

proxy = Proxy


-- Labels (attribute names) for the example
data Att_smin
data Att_ival
data Att_sres

smin = Label :: Label Att_smin
ival = Label :: Label Att_ival
sres = Label :: Label Att_sres

-- Labels for childs
data Ch_tree -- root
data Ch_r    -- node
data Ch_l    -- node
data Ch_i    -- leaf

ch_tree = Label :: Label (Ch_tree, Tree)
ch_r = Label :: Label (Ch_r, Tree)
ch_l = Label :: Label (Ch_l, Tree)
ch_i = Label :: Label (Ch_i, Int)
-- both the name and the type of the child are encoded


nt_Root = proxy :: Proxy Root
nt_Tree = proxy :: Proxy Tree

type SP = HList '[Att (Label Att_smin) Int,
            Att (Label Att_sres) Tree]
type IL = HList '[Att (Label Att_ival) Int]
type IR = HList '[Att (Label Att_ival) Int]

type IC = HList '[Chi (Label (Ch_l,Tree)) IL,
            Chi (Label (Ch_r,Tree)) IR]


type family UnWrap (l :: Type) :: [Type]
type instance UnWrap (HList l) = l
type Output_Node = Fam (UnWrap IC) (UnWrap SP)


-- Figure 6

leaf_smin (Fam chi par)
  = syndef smin (chi # ch_i)

node_smin (Fam chi par)
  = syndef smin (((chi # ch_l) # smin)
                  `min`
                 ((chi # ch_r) # smin))

root_ival (Fam chi par)
  = inhdef ival (nt_Tree .*. HNil)
                ((ch_tree .=. (chi # ch_tree) # smin)  .*.
                 emptyRecord)

node_ival (Fam chi par)
  = inhdef ival (nt_Tree .*. HNil)
                (ch_l .=.  par # ival .*.
                 ch_r .=.  par # ival .*.
                 emptyRecord)


root_sres (Fam chi par)
  = syndef sres ((chi # ch_tree ) # sres)


leaf_sres (Fam chi par)
  = syndef sres (Leaf (par # ival))


node_sres (Fam chi par)
  = syndef sres (Node ((chi # ch_l) # sres)
                      ((chi # ch_r) # sres))


data P_Root; p_Root = Label :: Label P_Root
data P_Node; p_Node = Label :: Label P_Node
data P_Leaf; p_Leaf = Label :: Label P_Leaf


--emptyRule ∷ Rule '[] '[] '[] '[] '[] '[]
emptyRule ∷ Rule '[Int] '[Bool] '[Bool] '[] '[] '[]
emptyRule = \r → id

emptyRule2 ∷ Rule '[Int] '[Bool] '[Bool] '[] '[] '[]
emptyRule2 = \r → id


aspect₁ = newLVPair p_Root emptyRule2 .*.
          newLVPair p_Node emptyRule .*.
          emptyRecord

aspect₂ = newLVPair p_Root emptyRule .*.
          newLVPair p_Leaf emptyRule .*.
          emptyRecord



testcomsingle = comSingle (Proxy :: Proxy True)
                          (newLVPair p_Node emptyRule)
                          aspect₁

testcom = aspect₁ ⊕ aspect₂

a1 = newLVPair p_Root emptyRule .*.
     emptyRecord

testcom2 = a1 ⊕ a1



-- Aspects definition for repmin

asp_smin = synAspect smin (nt_Tree .*. HNil)
                          (min:: Int -> Int -> Int)
                          (0::Int)
                          (p_Node .*. HNil)
           (p_Root .=. func .*. emptyRecord)

func = (\(Fam chi _) -> ((ch_tree .=. ((chi # ch_tree) # smin))
       .*. emptyRecord))


