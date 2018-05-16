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

> module Record where

> import Data.Kind 
> import Data.Type.Equality
> import Data.Proxy
> import Errors
> import Eq
> import Attribute
> import TPrelude
> import Data.Tagged
> import TagUtils

> data Record :: forall k . [(k,Type)] -> Type where
>   EmptyR :: Record '[]
>   ConsR  :: LabelSet ( '(l, v) ': xs) =>
>    Tagged l v -> Record xs -> Record ( '(l,v) ': xs)
                                                  


%if False
Some boilerplate to show Attributes and Attributions

> instance Show (Record '[]) where
>   show _ = "{}"

> instance (Show v, Show (Record xs)) =>
>          Show (Record ( '(l,v) ': xs ) ) where
>   show (ConsR lv xs) = let tail = show xs
>                             in "{" ++ show (unTagged lv) ++ "," ++ drop 1 tail 

%endif


--- HasField

> class HasFieldRec (l::k) (r :: [(k,Type)]) v | l r -> v where
>    hLookupByLabelRec:: Label l -> Record r -> v

> instance (HEqK l l1 b, HasFieldRec' b l ( '(l1,v1) ': r) v)
>     => HasFieldRec l ( '(l1,v1) ': r) v where
>     hLookupByLabelRec l (r :: Record ( '(l1,v1) ': r)) =
>          hLookupByLabelRec' (Proxy::Proxy b) l r

> 
> class HasFieldRec' (b::Bool) (l :: k) (r::[(k,Type)]) v | b l r -> v where
>     hLookupByLabelRec':: Proxy b -> Label l -> Record r -> v

> instance HasFieldRec' True l ( '(l,v) ': r) v where
>    hLookupByLabelRec' _ _ (ConsR (Tagged v) _) = v
> instance HasFieldRec l r v => HasFieldRec' False l ( '(l2,v2) ': r) v where
>    hLookupByLabelRec' _ l (ConsR _ r) = hLookupByLabelRec l r
 



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



> infixr 2 *.
> (*.) :: LabelSet ('(att, val) : atts) =>
>     Tagged att val -> Record atts -> Record ('(att, val) : atts)
> (*.) = ConsR



> class HasLabelRec (e :: k)(r ::[(k,Type)]) where
>   type HasLabelRecRes (e::k)(r ::[(k,Type)]) :: Bool
>   hasLabelRec :: Label e -> Record r -> Proxy (HasLabelRecRes e r)

> instance HasLabelRec e '[] where
>   type HasLabelRecRes e '[] = 'False
>   hasLabelRec _ _ = Proxy

> instance HasLabelRec  k ( '(k' ,v) ': ls) where
>   type HasLabelRecRes k ( '(k' ,v) ': ls)
>       = Or (k == k') (HasLabelRecRes k ls)
>   hasLabelRec _ _ = Proxy
