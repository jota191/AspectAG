
{-# LANGUAGE TemplateHaskell, CPP, DataKinds, KindSignatures, FlexibleInstances #-}

module TestTH where
import GHC.TypeLits
import Data.Proxy

import Language.Grammars.AspectAG.TH
import Language.Grammars.AspectAG

$(attLabel "ival" ''Int)
$(attPoly "pol")
$(attLabels [("lala",''Char),("lolo", ''Int)])
$(addNont "Expr")
