{-# LANGUAGE 
             TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             AllowAmbiguousTypes,
             ImplicitParams,
             ExtendedDefaultRules,
             UnicodeSyntax,
             DataKinds
#-}


module Main where

import System.Exit (exitFailure)
import Language.Grammars.AspectAG
import Test.QuickCheck
import Test.QuickCheck.Test
import Control.Monad

data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving (Show, Eq)

data Att_smin; smin = Label :: Label Att_smin
data Att_ival; ival = Label :: Label Att_ival
data Att_sres; sres = Label :: Label Att_sres
data Att_ssum; ssum = Label :: Label Att_ssum

-- Labels for childs
data Ch_tree -- root
data Ch_r    -- node
data Ch_l    -- node
data Ch_i    -- leaf

ch_tree = Label :: Label ( Ch_tree, Tree)
ch_r    = Label :: Label ( Ch_r, Tree)
ch_l    = Label :: Label ( Ch_l, Tree)
ch_i    = Label :: Label ( Ch_i, Int)
leafVal = Label :: Label ( Val, Int)


----non terminals
nt_Root = undefined :: Label Root
nt_Tree = undefined :: Label Tree

data P_Root; p_Root = Label :: Label (P_Root)
data P_Node; p_Node = Label :: Label (P_Node)
data P_Leaf; p_Leaf = Label :: Label (P_Leaf)  




root_ival (Fam chi par) =
  inhdef ival (nt_Tree .: ε) (  ch_tree .=.(chi # ch_tree # smin)
                            .*. emptyRecord)
  
node_ival (Fam chi par) =
  inhdef ival (nt_Tree .: ε) (  ch_l .=. par # ival
                            .*. ch_r .=. par # ival
                            .*. emptyRecord)

root_sres (Fam chi par)
  = syndef sres (chi # ch_tree # sres)

node_sres (Fam chi par)
  = syndef sres (Node (chi # ch_l # sres)(chi # ch_r # sres))

leaf_sres (Fam chi par)
  = syndef sres $ Leaf (par # ival)


node_smin (Fam chi par)
  = syndef smin $ (chi # ch_l # smin) `min` (chi # ch_r # smin)

leaf_smin (Fam chi par)
  = syndef smin $ chi # ch_i # leafVal

asp_ival =  p_Root .=. root_ival
        .*. p_Node .=. node_ival
        .*. emptyRecord
asp_sres =  p_Root .=. root_sres
        .*. p_Node .=. node_sres
        .*. p_Leaf .=. leaf_sres
        .*. emptyRecord
asp_smin =  p_Leaf .=. leaf_smin
        .*. p_Node .=. node_smin
        .*. emptyRecord

sem_Tree asp (Node l r) = knit (asp .#. p_Node)$
                           ch_l .=. sem_Tree asp l
                       .*. ch_r .=. sem_Tree asp r
                       .*. emptyRecord

sem_Tree asp (Leaf i)   = knit (asp .#. p_Leaf)$
                          ch_i .=. sem_Lit i .*. emptyRecord

sem_Root  asp (Root t) = knit (asp .#. p_Root)$
                         ch_tree .=. sem_Tree asp t .*. emptyRecord
        
sem_Lit :: Int -> Attribution p
        -> Attribution '[ '((Val, Int), Int)]
sem_Lit i _ = (leafVal =. i) *. emptyAtt
data Val


asp_repmin = asp_smin .+. asp_sres .+. asp_ival

examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                      (Node (Leaf 2) (Leaf 7))
                    )
                (Node (Node (Leaf (5)) (Leaf (27)))
                  (Leaf 6)
                )
              )


exampleT 0 = examplet
exampleT n = Node (exampleT (n-1)) (exampleT (n-1))

repmin t = sem_Root asp_repmin (Root t) emptyAtt # sres

minimo t = sem_Tree asp_smin t emptyAtt # smin



-- |A naive implementation of repmin, to test extensional equality against
-- our repmin function
naiveRepmin :: Tree -> Tree
naiveRepmin t = let min = minTree t
                in replaceT min t
                   
minTree :: Tree -> Int
minTree    (Leaf i)   = i
minTree    (Node l r) = minTree l `min` minTree r

replaceT :: Int -> Tree -> Tree 
replaceT m (Leaf _)   = Leaf m
replaceT m (Node l r) = Node (replaceT m l)(replaceT m r)


prop_minimo_correct :: Tree -> Bool
prop_minimo_correct t = minimo t == minTree t

prop_repmin_correct :: Tree -> Bool
prop_repmin_correct t = naiveRepmin t == repmin t

-- for testing
prop_falla :: Tree -> Bool
prop_falla = const False

-- TODO: improve this code to avoid if-then-else repetition if more tests
-- are added. Strings printed are ignored by cabal test,
-- and are only useful in manual running
main = verboseCheckResult prop_minimo_correct >>= \r ->
       if not $ isSuccess r
       then exitFailure
       else putStrLn "min tests passed" >>
            verboseCheckResult prop_repmin_correct >>= \r ->
            if not $ isSuccess r
            then exitFailure
            else putStrLn "repmin tests passed"
       
instance Arbitrary Tree where
  arbitrary = sized tree'
    where tree' 0 = liftM Leaf arbitrary
          tree' n | n>0 = 
                    oneof [liftM Leaf arbitrary,
                           liftM2 Node subtree subtree]
            where subtree = tree' (n `div` 2)
