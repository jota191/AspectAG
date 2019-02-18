{-|
Module      : Language.Grammars.AspectAG.TagUtils
Description : utilities for tagging values using a type level tag.
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

-}

{-# LANGUAGE DataKinds,
             TypeOperators,
             PolyKinds,
             GADTs,
             TypeInType,
             RankNTypes,
             StandaloneDeriving,
             FlexibleInstances,
             FlexibleContexts,
             ConstraintKinds,
             MultiParamTypeClasses,
             FunctionalDependencies,
             UndecidableInstances,
             ScopedTypeVariables,
             TypeFamilies
#-}

module Language.Grammars.AspectAG.TagUtils where
import Data.Tagged



-- | Labels are phantom  
data Label l = Label

-- | Get the label of a Tagged value, restricted to the case
--when labels are a pair, for safety, since this function is used
--on that context
labelLVPair :: Tagged (k1,k2) v -> Label (k1,k2)
labelLVPair _ = Label


-- |Get the first member of a pair label, as a label 
sndLabel :: Label (a,b) -> Label b
sndLabel _ = undefined

-- |Untag a value 
unTaggedChAtt :: Tagged l v -> v
unTaggedChAtt (Tagged v) = v

-- |Untag a value, different names to use on diferent contexts,
--in a future iteration possibly We'll have different Types of tag
unTagged :: Tagged l v -> v
unTagged (Tagged v) = v


-- | Get a label
label :: Tagged l v -> Label l
label _ = Label

-- | Same, mnemonically defined
labelTChAtt :: Tagged l v -> Label l
labelTChAtt _ = Label

-- | Pretty Constructor
infixr 4 .=.
(.=.) :: Label l -> v -> Tagged l v
l .=. v = Tagged v


