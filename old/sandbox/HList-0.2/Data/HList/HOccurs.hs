{-# LANGUAGE EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances,
  FlexibleContexts, UndecidableInstances #-}

{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Result-type-driven operations on typeful heterogeneous lists.
-}

module Data.HList.HOccurs where

import Data.HList.FakePrelude
import Data.HList.HListPrelude

{-----------------------------------------------------------------------------}

-- Zero or more occurrences

class HOccursMany e l
 where
  hOccursMany :: l -> [e]

instance HOccursMany e HNil
 where
  hOccursMany HNil = []

instance ( HOccursMany e l, HList l )
      =>   HOccursMany e (HCons e l)
 where
  hOccursMany (HCons e l) = e:hOccursMany l

instance ( HOccursMany e l, HList l )
      =>   HOccursMany e (HCons e' l)
 where
  hOccursMany (HCons _ l) = hOccursMany l


{-----------------------------------------------------------------------------}

-- One or more occurrences

class HOccursMany1 e l
 where
  hOccursMany1 :: l -> (e,[e])

instance ( HOccursMany e l, HList l )
      =>   HOccursMany1 e (HCons e l)
 where
  hOccursMany1 (HCons e l) = (e,hOccursMany l)

instance ( HOccursMany1 e l, HList l )
      => HOccursMany1 e (HCons e' l)
 where
  hOccursMany1 (HCons _ l) = hOccursMany1 l


{-----------------------------------------------------------------------------}

-- The first occurrence

class HOccursFst e l
 where
  hOccursFst :: l -> e

instance HList l
      => HOccursFst e (HCons e l)
 where
  hOccursFst (HCons e _) = e

instance ( HOccursFst e l, HList l )
      =>   HOccursFst e (HCons e' l)
 where
  hOccursFst (HCons _ l) = hOccursFst l


{-----------------------------------------------------------------------------}

-- One occurrence and nothing is left

class HOccurs e l
 where
  hOccurs :: l -> e

data TypeNotFound e

instance Fail (TypeNotFound e)
      => HOccurs e HNil
 where
  hOccurs = undefined

instance ( HList l
         , HOccursNot e l
         )
           => HOccurs e (HCons e l)
 where
  hOccurs (HCons e _) = e

instance ( HOccurs e l
         , HList l
         )
           => HOccurs e (HCons e' l)
 where
  hOccurs (HCons _ l) = hOccurs l


{-----------------------------------------------------------------------------}

-- One occurrence and nothing is left
-- A variation that avoids overlapping instances

class HOccurs' e l
 where
  hOccurs' :: l -> e

instance ( TypeEq e e' b
         , HOccursBool b e (HCons e' l) )
      =>   HOccurs' e (HCons e' l)
 where
  hOccurs' (HCons e' l) = e
   where
    e = hOccursBool b (HCons e' l)
    b = proxyEq (toProxy e) (toProxy e')

class HOccursBool b e l
 where
  hOccursBool :: b -> l -> e

instance ( HList l
         , HOccursNot e l
         )
           => HOccursBool HTrue e (HCons e l)
 where
  hOccursBool _ (HCons e _) = e

instance ( HOccurs' e l
         , HList l
         )
           => HOccursBool HFalse e (HCons e' l)
 where
  hOccursBool _ (HCons _ l) = hOccurs' l


{-----------------------------------------------------------------------------}

-- Zero or at least one occurrence

class HOccursOpt e l
 where
  hOccursOpt :: l -> Maybe e

instance HOccursOpt e HNil
 where
  hOccursOpt HNil = Nothing

instance HOccursOpt e (HCons e l)
 where
  hOccursOpt (HCons e _) = Just e

instance HOccursOpt e l
      => HOccursOpt e (HCons e' l)
 where
  hOccursOpt (HCons _ l) = hOccursOpt l


{-----------------------------------------------------------------------------}

-- Class to test that a type is "free" in a type sequence

data TypeFound e
class HOccursNot e l
instance HOccursNot e HNil
instance Fail (TypeFound e) => HOccursNot e (HCons e l)
instance HOccursNot e l => HOccursNot e (HCons e' l)


{-----------------------------------------------------------------------------}

class HProject l l'
 where
  hProject :: l -> l'

instance HProject l HNil
 where
  hProject _ = HNil

instance ( HList l'
         , HOccurs e l
         , HProject l l'
         )
      =>   HProject l (HCons e l')
 where
  hProject l = HCons (hOccurs l) (hProject l)


{-----------------------------------------------------------------------------}

-- Illustration of typical test scenarios

{-

Retrieve the Breed of an animal.

ghci-or-hugs> hOccurs myAnimal :: Breed
Cow

-}

{-

Normal hOccurs requires specification of the result type even if the result
type is determined by the fact that we are faced with a singleton list.

ghci-or-hugs> hOccurs (HCons 1 HNil)

<interactive>:1:
    No instance for (HOccurs e1 (HCons e HNil))

-}

{-

However, hOccurs can be elaborated as improved as follows:

ghci-or-hugs> hLookup (HCons 1 HNil)
1

-}

{-----------------------------------------------------------------------------}
