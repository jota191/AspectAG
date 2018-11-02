{-# LANGUAGE FlexibleContexts,
  DataKinds,
  GADTs,
  TypeFamilies,
  NoMonomorphismRestriction,
  OverloadedLists
#-}

module Main where

import Language.Grammars.AspectAG
import qualified Data.Set as S
import Test.QuickCheck
import Test.QuickCheck.Test
import Control.Monad
import System.Exit

-- | Data definition
-- We will code an EDSL for algebraic graphs, but instead of
-- use an ADT, to make the sintax actually extensible we use a type
-- for each production

-- instead of:

-- @
-- data Graph
--   = Empty | Vertex Int | Connect Graph Graph | Overlay Graph Graph
-- @

-- Let:
data Graph
  = Empty
  | Vertex Int
  | Overlay Graph Graph
  | Connect Graph Graph
  deriving (Show, Eq)

-- | Labels for productions
data P_Vertex  ; p_Vertex  = Label :: Label P_Vertex
data P_Empty   ; p_Empty   = Label :: Label P_Empty
data P_Overlay ; p_Overlay = Label :: Label P_Overlay
data P_Connect ; p_Connect = Label :: Label P_Connect

-- | Labels for children
data Ch_Vertex;    ch_Vertex    = Label :: Label (Ch_Vertex, Int)
data Ch_Empty;     ch_Empty     = Label :: Label (Ch_Empty, Graph)
data Ch_Overlay_L; ch_Overlay_L = Label :: Label (Ch_Overlay_L, Graph)
data Ch_Overlay_R; ch_Overlay_R = Label :: Label (Ch_Overlay_R, Graph)
data Ch_Connect_L; ch_Connect_L = Label :: Label (Ch_Connect_L, Graph)
data Ch_Connect_R; ch_Connect_R = Label :: Label (Ch_Connect_R, Graph)

-- | Labels for terminal symbols
data VInt; vint = Label :: Label (VInt, Int)
sem_VLit :: Int -> Attribution p -> Attribution '[ '((VInt, Int), Int)]
sem_VLit i _ = vint =. i *. emptyAtt

sem_Graph asp (Vertex i)
  = knit (asp .#. p_Vertex) $ ch_Vertex .=. sem_VLit i .*. emptyRecord

sem_Graph asp Empty
  = knit (asp .#. p_Empty) $ emptyRecord

sem_Graph asp (Overlay a b)
  = knit (asp .#. p_Overlay) $  ch_Overlay_L .=. sem_Graph asp a
                            .*. ch_Overlay_R .=. sem_Graph asp b
                            .*. emptyRecord

sem_Graph asp (Connect a b)
  = knit (asp .#. p_Connect) $  ch_Connect_L .=. sem_Graph asp a
                            .*. ch_Connect_R .=. sem_Graph asp b
                            .*. emptyRecord


-- | definition of graphs by adjacency lists, nodes are Ints, enough for our
-- purposes
data Rel = Rel {vert :: S.Set Int,
                adj  :: S.Set (Int,Int)}
           deriving (Show, Eq)


-- | a Graph is well defined if every edge refers to a proper vertex,
-- Algebraic Graphs will be allways well defined, so their traduction to Rels
-- must satisfy this preficate
wellDefined :: Rel -> Bool
wellDefined (Rel ver adj)
  = foldr (\(x,y) s-> S.insert x (S.insert y s)) S.empty adj `S.isSubsetOf` ver 


-- | Labels for attributes
data Att_srel; srel = Label :: Label Att_srel


-- | Attribute definition
vertex_srel (Fam c p)
  = syndef srel $ Rel [c # ch_Vertex # vint] []

empty_srel (Fam c p)
  = syndef srel $ Rel [] []

overlay_srel (Fam c p)
  = syndef srel $ let Rel v  l  = c # ch_Overlay_L # srel
                      Rel v' l' = c # ch_Overlay_R # srel
                  in  Rel (v `S.union` v') (l `S.union` l')

connect_srel (Fam c p)
  = syndef srel $ let Rel v  l  = c # ch_Connect_L # srel
                      Rel v' l' = c # ch_Connect_R # srel
                      conEdges  =
                        S.fromList [(ve, ve') |
                                     ve <- S.toList v, ve' <- S.toList v']
                  in  Rel (v `S.union` v') (l `S.union` l' `S.union` conEdges)

-- | The aspect to tranform an algebraic graph into a Rel
asp_srel
  =  p_Vertex  .=. vertex_srel
 .*. p_Overlay .=. overlay_srel
 .*. p_Connect .=. connect_srel
 .*. p_Empty   .=. empty_srel
 .*. emptyRecord

reify a
  = sem_Graph asp_srel a emptyAtt # srel

g1to2   = Connect (Vertex 1) (Vertex 2)
g12tot3 = (g1to2 `Connect` Vertex 3) `Overlay` (Vertex 3 `Connect` g1to2) 

-- | a test by hand
test_1 = reify g12tot3 == Rel {vert = S.fromList [1,2,3],
                            adj = S.fromList [(1,2),(1,3),(2,3),(3,1),(3,2)]}



-- | Arbitrary instance for Algebraic Graphs
instance Arbitrary Graph where
  arbitrary = sized graph'
    where graph' 0 = frequency [(1,pure Empty),(5,liftM Vertex arbitrary)]
          graph' n = oneof [liftM  Vertex arbitrary,
                            liftM2 Connect sub sub,
                            liftM2 Overlay sub sub]
            where sub = graph' (n `div` 2)


-- | by hand transformation
toRel (Empty)
  = Rel [] []
toRel (Vertex a)
  = Rel [a] []
toRel (Connect g h)
  = let Rel v e  = toRel g
        Rel w f  = toRel h
        newEdges = S.fromList [(t,u) | t <- S.toList v, u <- S.toList w]
    in Rel (v `S.union` w) (e `S.union` f `S.union` newEdges)
toRel (Overlay g h)
  = let Rel v e  = toRel g
        Rel w f  = toRel h
    in Rel (v `S.union` w) (e `S.union` f)

-- | Properties
prop_well_formedness :: Graph -> Bool
prop_well_formedness = wellDefined . reify

prop_correctness :: Graph -> Bool
prop_correctness g = reify g == toRel g


main
  = verboseCheckResult prop_well_formedness >>= \r ->
    if not $isSuccess r then exitFailure else putStrLn "well formedness ok"
    >>
    verboseCheckResult prop_correctness >>= \r ->
    if not $ isSuccess r then exitFailure else putStrLn "correctness ok"
