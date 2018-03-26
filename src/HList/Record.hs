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
             UndecidableInstances#-}

import Data.Kind 
import Data.Type.Equality (type (==))


--labels
data Label1
data Label2

data Proxy t = Proxy


data HRecord :: forall k . [(k,Type)] -> Type where
  EmptyR :: HRecord '[]
  ConsR  :: HLabelSet ( '(k, a) ': xs) =>
                        Proxy k -> a -> HRecord xs -> HRecord ( '(k,a) ':xs)


                                                  

v .*. r = ConsR (fst v) (snd v) r
infixr 2 .*.

test1 = ConsR (Proxy :: Proxy 'True) 'e' EmptyR
test2 = (Proxy :: Proxy 'True ,True) .*. (Proxy :: Proxy 'False,'r') .*. EmptyR
  :: HRecord '[ '( 'True ,Bool), '( 'False ,Char)]




-- LabelSet implementation over type-level lists of tuples where
-- the first coord is the proper label, the second one is not relevant
class HLabelSet (l :: [(k,Type)])
instance HLabelSet '[]
instance HLabelSet '[ '(x,v)]
instance ( HEqK l1 l2 leq
         , HLabelSet' '(l1,v1) '(l2,v2) leq r)
        => HLabelSet ( '(l1,v1) ': '(l2,v2) ': r)

class HLabelSet' l1v1 l2v2 (leq::Bool) r
instance ( HLabelSet ( '(l2,v2) ': r)
         , HLabelSet ( '(l1,v1) ': r)
         ) => HLabelSet' '(l1,v1) '(l2,v2) False r
instance ( Fail (DuplicatedLabel l1) ) => HLabelSet' l1 l2 True r

class Fail l
class DuplicatedLabel l

class HEq (x :: k) (y :: k) (b :: Bool) | x y -> b

-- | Equality for types that may have different kinds. This definition
-- allows operations on @Record [Tagged \"x\" a, Tagged 2 b]@ to work
-- as expected.

type HEqK (x :: k1) (y :: k2) (b :: Bool) = HEq (Proxy x) (Proxy y) b
instance ((Proxy x == Proxy y) ~ b) => HEq x y b
