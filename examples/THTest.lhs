



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


> $(addNont "Root")
> $(addNont "Tree")


> $(addProd "Leaf" ''Nt_Tree [("val", Ter ''Int)])
> $(addProd "Node" ''Nt_Tree [("l", NonTer ''Nt_Tree),("r", NonTer ''Nt_Tree)])
> $(addProd "Root" ''Nt_Root [("tree",NonTer ''Nt_Tree)])



> $(closeNTs [''Nt_Root,''Nt_Tree])




> $(mkSemFunc ''Nt_Tree)
> $(mkSemFunc ''Nt_Root)
