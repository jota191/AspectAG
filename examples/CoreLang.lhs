To use AspectAG in a module, some extensions must be enabled,
otherwise type errors we won't be readable.


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


> module CoreLang where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH


> $(addNont "Expr")
> $(addProd "EVar" ''Nt_Expr [("name", Ter ''String)])


> $(closeNTs [''Nt_Expr])
