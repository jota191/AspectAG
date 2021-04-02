{-|
Module      : Language.Grammars.AspectAG.Label
Description : Labels (polykinded, phantom)
Copyright   : (c) Juan García Garland, Marcos Viera 2020
License     : GPL-3
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX
-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module Data.GenRec.Label where
import Data.Proxy

data Label l = Label

sndLabel :: Label '(a,b) -> Label b
sndLabel _ = undefined

fstLabel :: Label '(a,b) -> Label a
fstLabel _ = undefined

labelFromType :: a -> Label a
labelFromType _ = Label

proxyToLabel :: Proxy a -> Label a
proxyToLabel _ = Label
