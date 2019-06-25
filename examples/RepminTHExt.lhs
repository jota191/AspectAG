> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE FlexibleContexts  #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}

> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}


> {-# LANGUAGE TypeApplications #-}


> module RepminTHExt where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import RepminTH hiding (Tree, semT, Leaf)

Extending the grammar: New production, a ternary node

> $(addProd "Node3" ''Nt_Tree [("l3", NonTer ''Nt_Tree),
>                              ("c3", NonTer ''Nt_Tree),
>                              ("r3", NonTer ''Nt_Tree)])

A support datatype

> data Tree3
>   = Node2 Tree3 Tree3
>   | Node3 Tree3 Tree3 Tree3
>   | Leaf Int

semantic function for the new production

> semTree_Node3 asp l c r
>   =   knitAspect p_Node3 asp
>  $    ch_l3 .=. l
>  .*.  ch_c3 .=. c
>  .*.  ch_r3 .=. r
>  .*.  EmptyRec

> semT asp (Node2 l r)
>   = semTree_Node asp (semT asp l) (semT asp r)
> semT asp (Node3 l c r)
>   = semTree_Node3 asp (semT asp l) (semT asp c) (semT asp r)
> semT asp (Leaf i)
>   = semTree_Leaf asp (sem_Lit i)

> asp_repmin3
>  =    syn sres p_Node3 (do x <- at ch_l3 sres
>                            y <- at ch_c3 sres
>                            z <- at ch_r3 sres
>                            return (Node x (Node y z)))
>  .+: syn smin p_Node3 (min3  <$> at ch_l3 smin
>                              <*> at ch_c3 smin
>                              <*> at ch_r3 smin)
>  .+: inh ival p_Node3 ch_l3 (at lhs ival)
>  .+: inh ival p_Node3 ch_c3 (at lhs ival)
>  .+: inh ival p_Node3 ch_r3 (at lhs ival)
>  .+: asp_repmin
>  where min3 a b c = a `min` b `min` c

-- TODO: invert arg order


> repmin'' t = semR3 asp_repmin3 (Root3 t) emptyAtt #. sres
> data Root3 = Root3 Tree3
> semR3 asp (Root3 t) = semRoot_Root asp (semT asp t)
