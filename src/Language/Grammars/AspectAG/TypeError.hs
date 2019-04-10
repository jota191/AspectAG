
{-|

Module      : Language.Grammars.AspectAG.TypeError
Description : Main module, First-class attribute grammars
Copyright   : (c) Juan García Garland, 2019 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX


The original version of the library is documented in the paper:
/Attribute Grammars Fly First-Class.
How to do aspect oriented programming in Haskell/

This was implemented from scratch using the improvements on GHC on the last
10 years, allowing a broad set of techniques for doing type level programming.

-}

{-# LANGUAGE TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             UnicodeSyntax,
             DataKinds,
             TypeOperators,
             PolyKinds,
             GADTs,
             MultiParamTypeClasses,
             FlexibleContexts,
             FlexibleInstances,
             UndecidableInstances
#-}

module Language.Grammars.AspectAG.TypeError where
import Language.Grammars.AspectAG.HList
import Language.Grammars.AspectAG.Attribution
import Language.Grammars.AspectAG.Record
import Language.Grammars.AspectAG.Attribute
import Data.Kind
import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.TPrelude
import Data.Proxy
import Language.Grammars.AspectAG.ChildAtts
import Language.Grammars.AspectAG.TagUtils
import Language.Grammars.AspectAG.GenRecord
import GHC.TypeLits




-- | No field on record, On AAG usually appears when an aspect was not
-- defined in all its required labels
instance TypeError
  ( Text "Type Error : No Field found on Record:" :$$:
    Text "(Possibly, in some aspect there are productions " :<>:
    Text "where the attribute is undefined)" :$$:
    Text "No Field of type " :<>: ShowType l
    :<>: Text " on Record" )
  => UpdateAtLabelRec l v '[] '[] where
  updateAtLabelRec _ _ r = r

-- | TypeError

instance TypeError ( Text "Type Error : No Child Found on Production:" :$$:
    Text "(Possibly, in some production there is a reference to a child " :<>:
    Text "that does not exist, or the attribute is not defined there)" :$$:
    Text "No Child of type " :<>: ShowType l
    :<>: Text " on Attribution" )
  => HasChildF l '[] where
   type LookupByChildFR l '[] = TypeError (Text "Look at the previous error")
   lookupByChildF = undefined


type NoAttToUpdate l r
  = Text "No attribute of name '" :<>: ShowType l :<>: Text "'":$$:
          Text "to update on Attribution: " :<>: ShowType r

instance UpdateAtLabelAttF l v '[] where
  type UpdateAtLabelAttFR l v '[] = TypeError (NoAttToUpdate l '[])
  updateAtLabelAttF = undefined


instance TypeError (Text "LabelSet Error:" :$$:
                    Text "Duplicated Label on Record" :$$:
                    Text "On fields:" :$$: ShowType l1 :$$:
                    Text " and " :$$: ShowType l1 )
          => LabelSet' l1 l2 True r


-- data IncorrectDef l lch err
-- data UndefNT t
-- data UndefProd t
-- data UndefAtt t

-- instance Fail (IncorrectDef l lch (UndefNT t)) 
--          => SingleDef HTrue HFalse (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
--  singledef = undefined

-- instance Fail (IncorrectDef l lch (UndefProd (lch,t))) 
--          => SingleDef HFalse HTrue (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
--  singledef = undefined
