> {-# LANGUAGE TypeOperators #-}




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
> {-# LANGUAGE PartialTypeSignatures     #-}


> module TreeInt  where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH
> import Language.Grammars.AspectAG.HList


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
> $(addProd "Branch" ''Nt_Tree [("branch_l", NonTer ''Nt_Tree),
>                               ("branch_r", NonTer ''Nt_Tree)])
> $(addProd "Node" ''Nt_Tree   [("node_l",   NonTer ''Nt_Tree),
>                               ("node_val", Ter    ''Int),
>                               ("node_r",   NonTer ''Nt_Tree)])
> $(addProd "Root" ''Nt_Root   [("tree",NonTer ''Nt_Tree)])

> $(closeNTs [''Nt_Root, ''Nt_Tree])

> $(mkSemFuncs [''Nt_Tree, ''Nt_Root])


> -- | PrettyPrint
> $(attLabels [("pp", ''String)])
> asp_pp =
>   syn pp p_Leaf (show <$> ter ch_val)
>   .+:
>   syn pp p_Branch ( do l <- at  ch_branch_l pp
>                        r <- at  ch_branch_r pp
>                        return $ "(" ++ l ++ " ^ " ++ r ++ ")"
>                   )
>   .+:
>   syn pp p_Node   ( do l <- at  ch_node_l pp
>                        r <- at  ch_node_r pp
>                        v <- ter ch_node_val
>                        return $ "(" ++ l ++ " <" ++ show v ++ "> " ++ r ++ ")"
>                   )
>   .+:
>   emptyAspect


> printIntTree t = sem_Tree asp_pp t emptyAtt #. pp

> exampleT = Node (Branch (Leaf 4)
>                         (Leaf 5)
>                 )
>                 3
>                 (Node (Node (Leaf 9)
>                             7
>                             (Leaf 13))
>                       5
>                       (Leaf 16)
>                 )



> -- | Size
> $(attLabel "ssize" ''Int)
> asp_size =
>   (syn ssize p_Leaf $ pure 1)
>   .+:
>   (syn ssize p_Branch $ (+) <$> at ch_branch_l ssize
>                             <*> at ch_branch_r ssize)
>   .+:
>   (syn ssize p_Node $ plus3 <$> at ch_node_l ssize
>                             <*> pure 1
>                             <*> at ch_node_r ssize)
>   .+: emptyAspect
>   where plus3 a b c = a + b + c

> size t = sem_Tree asp_size t emptyAtt #. ssize

> infixr 2 .:..
> (.:..) :: Label (p :: Prod) -> KList l -> KList (p ': l)
> (.:..) = KCons

