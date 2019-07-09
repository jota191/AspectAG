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


> module List where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import Prelude hiding (head, tail, sum, all, length,null, last)


> $(addNont "List")

> $(addProd "Nil"  ''Nt_List [])
> $(addProd "Cons" ''Nt_List [("head", Poly), ("tail", NonTer ''Nt_List)])

Does not work:

> $(closeNTs [''Nt_List])

Parametric ASTs are not yet derivable from TH

