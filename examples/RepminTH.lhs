



To use AspectAG in a module, some extensions must be enabled,
otherwise type errors we won't have readable type errors.


> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE FlexibleContexts  #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}

> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# LANGUAGE DataKinds #-}

> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeApplications #-}


> module RepminTH where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH


To add a nonterminal we can use the TH function |addNont|:

> $(addNont "Root")
> $(addNont "Tree")

The produce the following code:

< type Nt_Root = NT "Root"
< nt_Root = Label :: Label Nt_Root

< type Nt_Tree = NT "Tree"
< nt_Tree = Label :: Label (Nt_Tree)


After, we generate productions:


> $(addProd "Leaf" ''Nt_Tree [("val", Ter ''Int)])
> $(addProd "Node" ''Nt_Tree [("l", NonTer ''Nt_Tree),("r", NonTer ''Nt_Tree)])
> $(addProd "Root" ''Nt_Root [("tree",NonTer ''Nt_Tree)])


Semantic functions and a datatype by hand (for now)

> data Root = Root Tree deriving Show
> data Tree = Leaf Int | Node Tree Tree deriving Show


> sem_Root asp (Root t)
>  = knitAspect p_Root asp $ ch_tree .=. sem_Tree asp t .*. EmptyRec

> sem_Tree asp (Leaf i)
>  = knitAspect p_Leaf asp $ ch_val .=. sem_Lit i .*. EmptyRec
> sem_Tree asp (Node l r)
>  = knitAspect p_Node asp
>  $   ch_l .=. sem_Tree asp l
>  .*. ch_r .=. sem_Tree asp r
>  .*. EmptyRec


> $(attLabels [("sres", ''Tree), ("smin", ''Int), ("ival", ''Int)])

> asp_smin
>  =   syn smin p_Node (min @ Int <$> at ch_l smin <*> at ch_r smin)
>  .+: syn smin p_Leaf (ter ch_val)
>  .+: emptyAspect

> asp_sres
>  =    syn sres p_Node (Node <$> at ch_l sres <*> at ch_r sres)
>  .+:  syn sres p_Leaf (Leaf <$> at lhs ival)
>  .+:  syn sres p_Root (at ch_tree sres)
>  .+:  emptyAspect

> asp_ival
>  =    inh ival p_Root ch_tree (at ch_tree smin)
>  .+:  inh ival p_Node ch_l (at lhs ival)
>  .+:  inh ival p_Node ch_r (at lhs ival)
>  .+:  emptyAspect

> asp_repmin
>   = asp_smin .:+: asp_sres .:+: asp_ival

> repmin t
>   = sem_Root asp_repmin (Root t)
>          emptyAtt #. sres


Another way to build  semantic functions:

> semRoot_Root asp tree
>  = knitAspect p_Root asp
>  $ ch_tree .=. tree .*. EmptyRec

> semTree_Node asp l r
>  = knitAspect p_Node asp
>  $    ch_l .=. l
>  .*.  ch_r .=. r
>  .*.  EmptyRec

> semTree_Leaf asp i
>  = knitAspect p_Leaf asp
>  $ ch_val .=. i .*. EmptyRec

> semR asp (Root t)    = semRoot_Root asp (semT asp t)
> semT asp (Node l r)  = semTree_Node asp (semT asp l) (semT asp r)
> semT asp (Leaf i)    = semTree_Leaf asp (sem_Lit i)


> repmin' t = sem_Root asp_repmin (Root t) emptyAtt #. sres
