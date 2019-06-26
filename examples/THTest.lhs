



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


> $(createConstant "Lolo")
> $(closeNT ''Nt_Root)
> $(closeNT ''Nt_Tree)
