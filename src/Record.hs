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

data Proxy a = Proxy


data HRecord :: [Type] -> Type where -- TODO: Kind polymorphic?
  EmptyR :: HRecord '[]
  ConsR  :: Proxy l -> a
    -> HRecord xs -> HRecord ((l,a)':xs)

(*.) :: HLabelSet ((l, a) : xs)
        =>(Proxy l, a) -> HRecord xs -> HRecord ((l, a) : xs)
v *. r = ConsR (fst v) (snd v) r
infixr 2 *.

test2 = (Proxy,True) *. (Proxy,'r') *. EmptyR
  :: HRecord '[(Int,Bool), (Bool,Char)]




-- LabelSet implementation over type-level lists of tuples where
-- the first coord is the proper label, the second one is not relevant
class HLabelSet (l :: [Type])
instance HLabelSet '[]
instance HLabelSet '[(x,v)]
instance ( HEqK l1 l2 leq
         , HLabelSet' (l1,v1) (l2,v2) leq r)
        => HLabelSet ((l1,v1) ': (l2,v2) ': r)

class HLabelSet' l1v1 l2v2 (leq::Bool) r
instance ( HLabelSet ((l2,v2) ': r)
         , HLabelSet ((l1,v1) ': r)
         ) => HLabelSet' (l1,v1) (l2,v2) False r
instance ( Fail (DuplicatedLabel l1) ) => HLabelSet' l1 l2 True r

class Fail l
class DuplicatedLabel l


instance Show (HRecord '[]) where
    show _ = "R[]"

instance (Show e, Show (HRecord l)) => Show (HRecord ((k,e) ': l)) where
    show (ConsR p x l) = let 'R':'[':s = show l
                         in "H[" ++ show x ++
                                  (if s == "]" then s else "," ++ s)

class HEq (x :: k) (y :: k) (b :: Bool) | x y -> b

-- | Equality for types that may have different kinds. This definition
-- allows operations on @Record [Tagged \"x\" a, Tagged 2 b]@ to work
-- as expected.

type HEqK (x :: k1) (y :: k2) (b :: Bool) = HEq (Proxy x) (Proxy y) b
instance ((Proxy x == Proxy y) ~ b) => HEq x y b
