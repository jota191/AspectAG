{-|
Module      : Language.Grammars.AspectAG.TPrelude
Description : Some type level functions, needed for AspectAG
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX


-}
{-# LANGUAGE GADTs,
             KindSignatures,
             TypeOperators,
             TypeFamilies,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             StandaloneDeriving,
             UndecidableInstances,
             FunctionalDependencies,
             ConstraintKinds,
             ScopedTypeVariables,
             PolyKinds,
             DataKinds
#-}

module Language.Grammars.AspectAG.TPrelude where
import Data.Kind
import Data.Type.Equality
import GHC.TypeLits
import Data.Proxy

-- | If construction, purely computed at type level
type family If (cond:: Bool) (thn :: k) (els :: k) :: k where
  If 'True  thn els = thn
  If 'False thn els = els

-- | Or, purely computed at type level
type family Or (l :: Bool)(r :: Bool) :: Bool where
  Or False b = b
  Or True b  = 'True

-- | And, purely computed at type level
type family And (l :: Bool)(r :: Bool) :: Bool where
  And False b = False
  And True b  = b

-- | Not, purely computed at type level
type family Not (l :: Bool) :: Bool where
  Not False = True
  Not True  = False


-- | LabelSet is a predicate over lists of pairs.
--We assume the list represent a (partial) mapping from k1 to k2.
--k1 is a label, k2 possibly a value.
--The first member of each pair must be unique, this is a predicate of
--well formedness
-- class LabelSet (l :: [(k1,k2)])

-- -- | The empty set is a valid mapping
-- instance LabelSet '[]

-- -- | A singleton set is a valid mapping, defined only in one point.
-- instance LabelSet '[ '(x,v)] 



-- instance ( {-HEqK l1 l2 leq
--          ,-} LabelSet' '(l1,v1) '(l2,v2) (l1==l2) r)
--         => LabelSet ( '(l1,v1) ': '(l2,v2) ': r)

-- class LabelSet' l1v1 l2v2 (leq::Bool) r
-- instance ( LabelSet ( '(l2,v2) ': r)
--          , LabelSet ( '(l1,v1) ': r)
--          ) => LabelSet' '(l1,v1) '(l2,v2) False r

type family LabelSetF (r :: [(k, k')]) :: Bool where
  LabelSetF '[] = True
  LabelSetF '[ '(l, v)] = True
  LabelSetF ( '(l, v) ': '(l', v') ': r) = And3 (Not (l == l')) 
                                                (LabelSetF ( '(l, v)   ': r) )
                                                (LabelSetF ( '(l', v') ': r) )


class LabelSet (r :: [(k, k')]) where {}
instance LabelSetF r ~ True => LabelSet r

type family And3 (a1 :: Bool) (a2 :: Bool) (a3 :: Bool) where
  And3 True True True  = True
  And3 _     _   _     = False
                                                 
-- | Predicate of membership, for lists at type level
type family HMemberT (e::k)(l ::[k]) :: Bool where
  HMemberT k '[] = 'False
  HMemberT k ( k' ': l) = If (k==k') 'True (HMemberT k l)


-- | Predicate of membership, for labels at type level
type family HasLabelT (l::k) (lst :: [(k,Type)]) :: Bool where
  HasLabelT l '[] = 'False
  HasLabelT l ( '(k,v) ': tail) = If (l == k) 'True (HasLabelT l tail)


-- |This is used for type Equality
class HEq (x :: k) (y :: k) (b :: Bool) | x y -> b
type HEqK (x :: k1) (y :: k2) (b :: Bool) = HEq (Proxy x) (Proxy y) b
instance ((Proxy x == Proxy y) ~ b) => HEq x y b

type family HEqKF (a :: k)(b :: k) :: Bool
type instance HEqKF a b = a == b


-- | heterogeneous equality at type level
type family (a :: k1) === (b :: k2) where
  a === b = (Proxy a) == (Proxy b)


type family TPair (a :: k) b where
  TPair a b = '(a, b)
