%if False

> {-# LANGUAGE DataKinds,
>              TypeOperators,
>              PolyKinds,
>              GADTs,
>              TypeInType,
>              RankNTypes,
>              StandaloneDeriving,
>              FlexibleInstances,
>              FlexibleContexts,
>              ConstraintKinds,
>              MultiParamTypeClasses,
>              FunctionalDependencies,
>              UndecidableInstances,
>              ScopedTypeVariables,
>              TypeFamilies
> #-}

> module ChildAtts where

> import Data.Kind 
> import Data.Type.Equality
> import Data.Proxy
> import Errors
> import Eq
> import Attribute
> import TPrelude
> import Data.Tagged
> import Attribution


> -- Tags a Label to an attribution, used for children
> data TaggedChAttr (l::k) (v :: [(k,Type)]) :: Type where
>   TaggedChAttr :: Label l -> Attribution v -> TaggedChAttr l v
> unTaggedChAttr :: TaggedChAttr l v -> Attribution v
> unTaggedChAttr (TaggedChAttr _ v) = v


> -- the record of attribution fot the children
> data ChAttsRec :: forall k . [(k , [(k,Type)])] -> Type where
>   EmptyCh :: ChAttsRec '[]
>   ConsCh  :: LabelSet ( '(l, v) ': xs) =>
>    TaggedChAttr l v -> ChAttsRec xs -> ChAttsRec ( '(l,v) ': xs)


%if False
Some boilerplate to show Attributes and Attributions


> instance Show (ChAttsRec '[]) where
>   show _ = "{}"

> instance (Show (Attribution v), Show (ChAttsRec xs)) =>
>          Show (ChAttsRec ( '(l,v) ': xs ) ) where
>   show (ConsCh lv xs) = let tail = show xs
>                             in "{" ++ show (unTaggedChAttr lv) ++ "," ++ drop 1 tail 

%endif

--- HasField

> class HasChild (l::k) (r :: [(k ,[(k,Type)])]) v | l r -> v where
>    hLookupByChild:: Label l -> ChAttsRec r -> Attribution v

> instance (HEqK l l1 b, HasChild' b l ( '(l1,v1) ': r) v)
>     => HasChild l ( '(l1,v1) ': r) v where
>     hLookupByChild l (r :: ChAttsRec ( '(l1,v1) ': r)) =
>          hLookupByChild' (Proxy::Proxy b) l r

> 
> class HasChild' (b::Bool) (l :: k) (r::[(k,[(k,Type)])]) v | b l r -> v where
>     hLookupByChild':: Proxy b -> Label l -> ChAttsRec r -> Attribution v

> instance HasChild' True l ( '(l,v) ': r) v where
>    hLookupByChild' _ _ (ConsCh lv _) = unTaggedChAttr lv
> instance HasChild l r v => HasChild' False l ( '(l2,v2) ': r) v where
>    hLookupByChild' _ l (ConsCh _ r) = hLookupByChild l r
 
> {-



UPDATEATLABEL

> class UpdateAtLabelRec (l :: k)(v :: Type)(r :: [(k,Type)])(r' :: [(k,Type)])
>    | l v r -> r' where
>   updateAtLabelRec :: Label l -> v -> Record r -> Record r'

So we need an auxiliary class with an extra parameter to decide if we update
on the head of r or not

> class UpdateAtLabelRec' (b::Bool)(l::k)(v::Type)(r::[(k,Type)])(r'::[(k,Type)])
>     | b l v r -> r'  where
>   updateAtLabelRec' :: Proxy b -> Label l -> v -> Record r -> Record r'



> instance (HEqK l l' b, UpdateAtLabelRec' b l v ( '(l',v')': r) r')
>  -- note that if pattern over r is not written this does not compile
>        => UpdateAtLabelRec l v ( '(l',v') ': r) r' where
>   updateAtLabelRec = updateAtLabelRec' (Proxy :: Proxy b)


> instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
>          UpdateAtLabelRec' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
>   updateAtLabelRec' _ (l :: Label l) v (att `ConsR` atts)
>     = (Tagged v :: Tagged l v) `ConsR` atts

> 
> instance ( UpdateAtLabelRec l v r r', LabelSet  ( a ': r' ) ) =>
>          UpdateAtLabelRec' False l v ( a ': r) ( a ': r') where
>   updateAtLabelRec' (b :: Proxy False) (l :: Label l) (v :: v)
>     (ConsR att xs :: Record ( a ': r))
>     = case (updateAtLabelRec l v xs) of
>         xs' -> ConsR att xs' :: Record( a ': r')

> instance Fail (FieldNotFound l) => UpdateAtLabelRec l v '[] '[] where
>     updateAtLabelRec _ _ r = r



%if True

Some tests
%endif

> infixr 2 *.
> (*.) :: LabelSet ('(att, val) : atts) =>
>     Tagged att val -> Record atts -> Record ('(att, val) : atts)
> (*.) = ConsR

TODO: cambiar nombre de params aca

> infixr 4 =.
> (=.) :: Label l -> v -> Tagged l v
> (Label :: Label l) =. (v::v) = Tagged v :: Tagged l v


> -}
