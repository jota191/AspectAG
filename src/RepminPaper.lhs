%if False

> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE
>             TypeFamilies,
>              FlexibleContexts,
>              ScopedTypeVariables,
>              NoMonomorphismRestriction,
>              ImplicitParams,
>              ExtendedDefaultRules,
>              UnicodeSyntax,
>              DataKinds,
>              TypeApplications,
>              PartialTypeSignatures
> #-}

> module Repmin where
> import Language.Grammars.AspectAG2
> import Control.Monad
> import Control.Applicative
> import Data.Proxy
> import GHC.TypeLits

%endif

\todo{hay que presentar el problema repmin}


Attribute grammars were originally introduced to describe semantics for context
free languages. Given a grammar, we associate attributes to each production.
Attribute values are computed from semantic rules given by the implementator in
every node of the abstract syntax tree in terms of the attribute values of the
children and the parent. Attribute grammars can be viewed also as a
general-purpose formalism for describing recursive computations over data types.

\todo{ reescribir esto, se lo copie a Marcos :)
Functional programs can easily be extended by defining extra functions. If
however a data type is extended with a new alternative, each parameter position
and each case expression where a value of this type is matched has to be
inspected and modified accordingly. In object oriented programing the situation
is reversed: if we implement the alternatives of a data type by sub-classing, it
is easy to add a new alternative by defining a new subclass in which we define a
method for each part of desired global functionality. If however we want to
define a new function for a data type, we have to inspect all the existing
subclasses and add a method describing the local contribution to the global
computation over this data type. This problem was first noted by Reynolds [REF]
and later referred to as “the expression problem” by Wadler [REF].
}


As a running example consider the well known {\tt repmin} problem[REF]. Given a tree,
for example a binary tree containing integer values on its leaves.
repmin must compute a tree with the same shape containing the global minimum in
every leaf. {\tt repmin} was introduced as an example of a circular program [REF]?,
i.e. a program where part of the result is used as input.


Consider the Haskell definition of a grammar for trees.

> data Root
>   = Root Tree

%if False

> deriving (Show, Eq)

%endif

> data Tree = Leaf Int
>           | Node Tree Tree

%if False

> deriving (Show, Eq)

%endif




> smin  = Label  ('Att "smin" Int)
> sres  = Label  ('Att "sres" Tree)
> ival  = Label  ('Att "ival" Int)


%if False


type P_Node = 'Prd "p_Node" ('NT "Tree")
p_Node = Label @ P_Node

type P_Leaf = 'Prd "p_Leaf" ('NT "Tree")
p_Leaf = Label @ P_Leaf

type P_Root = 'Prd "p_Root" ('NT "Root")
p_Root = Label @ P_Root

type Nt_Tree = 'NT "Tree"

ch_l    = Label @ ('Chi "ch_l"    P_Node ('Left Nt_Tree))
ch_r    = Label @ ('Chi "ch_r"    P_Node ('Left Nt_Tree))
ch_tree = Label @ ('Chi "ch_tree" P_Root ('Left Nt_Tree))
ch_i    = Label @ ('Chi "ch_i"    P_Leaf ('Right ('T Int)))





data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving (Show, Eq)

examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                      (Node (Leaf 2) (Leaf 7))
                    )
                (Node (Node (Leaf (5)) (Leaf (27)))
                  (Leaf 6)
                )
              )

smin = Label @ ('Att "smin" Int)
sres = Label @ ('Att "sres" Tree)
ival = Label @ ('Att "ival" Int)

type P_Node = 'Prd "p_Node" ('NT "Tree")
p_Node = Label @ P_Node

type P_Leaf = 'Prd "p_Leaf" ('NT "Tree")
p_Leaf = Label @ P_Leaf

type P_Root = 'Prd "p_Root" ('NT "Root")
p_Root = Label @ P_Root

type Nt_Tree = 'NT "Tree"

ch_l    = Label @ ('Chi "ch_l"    P_Node ('Left Nt_Tree))
ch_r    = Label @ ('Chi "ch_r"    P_Node ('Left Nt_Tree))
ch_tree = Label @ ('Chi "ch_tree" P_Root ('Left Nt_Tree))
ch_i    = Label @ ('Chi "ch_i"    P_Leaf ('Right ('T Int)))

sem_Tree' asp (Node l r)
  = knit' (asp .#. p_Node)
      $   ch_l  .=. sem_Tree' asp l
     .*.  ch_r  .=. sem_Tree' asp r
     .*.  EmptyRec
sem_Tree' asp (Leaf i)
  = knit' (asp .#. p_Leaf)
      $   ch_i  .=. sem_Lit i
     .*.  EmptyRec
sem_Root' asp (Root r)
  = knit' (asp .#. p_Root)
      $   ch_tree  .=. sem_Tree' asp r
     .*.  EmptyRec

sem_Tree asp (Node l r) = knitAspect p_Node asp
                           $  ch_l .=. sem_Tree asp l
                          .*. ch_r .=. sem_Tree asp r
                          .*.  EmptyRec
sem_Tree asp (Leaf i)   = knitAspect p_Leaf asp$
                          ch_i .=. sem_Lit i .*. EmptyRec
sem_Root asp (Root r)   = knitAspect p_Root asp$
                          ch_tree .=. sem_Tree asp r .*. EmptyRec


-- | rules for smin
--node_smin
--  = syndefM smin p_Node $ min <$> at ch_l smin <*> at ch_r smin

node_smin
  = use smin p_Node (KCons (Proxy @ Nt_Tree) KNil) min 0
leaf_smin
  = syndefM smin p_Leaf $ at ch_i lit

-- | rules for sres
node_sres
  = syndefM sres p_Node $ Node <$> at ch_l sres <*> at ch_r sres
leaf_sres
  = syndefM sres p_Leaf $ Leaf <$> at lhs ival
root_sres
  = syndefM sres p_Root $ at ch_tree sres

-- | rules for ival
root_ival
  = inhdefM ival p_Root ch_tree $ at ch_tree smin
node_ival_l
  = inhdefM ival p_Node ch_l $ at lhs ival
node_ival_r
  = inhdefM ival p_Node ch_r $ at lhs ival

-- | Aspects


asp_smin = updCAspect (Proxy @ ('Text "smin"))
    $   node_smin
   .+:  leaf_smin
   .+:  emptyAspect

asp_sres = updCAspect (Proxy @ ('Text "sres"))
    $   node_sres
   .+:  leaf_sres
   .+:  root_sres
   .+:  emptyAspect

asp_ival = updCAspect (Proxy @ ('Text "ival"))
    $   node_ival_l
   .+:  node_ival_r
   .+:  root_ival
   .+:  emptyAspect

node_smin'
  = synmodM smin p_Node $ max <$> at ch_l smin <*> at ch_r smin

asp_repmin = updCAspect (Proxy @ ('Text "repmin"))
    $   asp_smin
  .:+:  asp_sres
  .:+:  asp_ival

repmin t
  = sem_Root asp_repmin (Root t) emptyAtt #. sres

minimo t
  = sem_Tree asp_smin t emptyAtt #. smin



ssiz = Label @ ('Att "ssiz" Int)

asp_ssiz =   syndefM ssiz p_Leaf (pure 1)
        .+: (syndefM ssiz p_Node (at ch_l ssiz <**> pure (+) <*> at ch_r ssiz))
        .+: emptyAspect

repavg t = sem_Root asp_repavg (Root t) emptyAtt #. sres
  where asp_repavg  = ival' .+: asp_ssiz .:+: asp_ssum .:+: asp_repmin
        ival'       = inhmodM ival p_Root ch_tree
            $ div <$> at ch_tree ssum <*> at ch_tree ssiz

ssum = Label @ ('Att "ssum" Int)
asp_ssum
  =  syndefM ssum p_Node (at ch_l ssum <**> pure (+) <*> at ch_r ssum)
 .+: syndefM ssum p_Leaf (at ch_i lit)
 .+: emptyAspect

{-
size t = sem_Tree asp_ssiz t emptyAtt #. ssiz

ssum = Label @ ('Att "ssum" Int)
asp_ssum
  =  syndefM ssum p_Node (at ch_l ssum <**> pure (+) <*> at ch_r ssum)
 .+: syndefM ssum p_Leaf (at ch_i lit)
 .+: emptyAspect


-- defines ival in another way
root_avg = inhdefM ival p_Root ch_tree
 $ do zi <- at ch_tree ssiz
      su <- at ch_tree ssum
      pure $ su `div` zi

repavg t = sem_Root repavg (Root t) emptyAtt #. sres
  where repavg =  node_ival_l
              .+: node_ival_r
              .+: root_avg
              .+: asp_ssiz .:+: asp_sres .:+: asp_ssum

spoly :: Proxy a -> Label ('Att "spoly" a)
spoly _ = Label

getProxy :: a -> Proxy a
getProxy _ = Proxy
-}

%endif
