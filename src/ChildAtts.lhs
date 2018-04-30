% if False

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
> --import Data.Tagged
> import Attribution

> --TODO: move this
> -- Tags a Label to an attribution, used for children
> data TaggedChAttr (l::k) (v :: [(k,Type)]) :: Type where
>   TaggedChAttr :: Label l -> Attribution v -> TaggedChAttr l v
> unTaggedChAttr :: TaggedChAttr l v -> Attribution v
> unTaggedChAttr (TaggedChAttr _ v) = v

> data TaggedChAtt :: (k,Type) -> Type where
>   TaggedChAtt :: Label l -> v -> TaggedChAtt '(l,v)
> unTaggedChAtt :: TaggedChAtt '(l, v) -> v
> unTaggedChAtt (TaggedChAtt _ v) = v
> labelTChAtt :: TaggedChAtt '(l,v) -> Label l
> labelTChAtt _ = Label


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
 


UPDATEATLABEL

> class UpdateAtChild (l :: k)(v :: [(k,Type)])
>       (r :: [(k,[(k,Type)])])(r' :: [(k,[(k,Type)])])
>    | l v r -> r' where
>   updateAtChild :: Label l -> Attribution v -> ChAttsRec r -> ChAttsRec r'

So we need an auxiliary class with an extra parameter to decide if we update
on the head of r or not

> class UpdateAtChild' (b::Bool)(l::k)(v::[(k,Type)])
>       (r::[(k,[(k,Type)])])(r'::[(k,[(k,Type)])])
>     | b l v r -> r'  where
>   updateAtChild' :: Proxy b -> Label l -> Attribution v -> ChAttsRec r -> ChAttsRec r'



> instance (HEqK l l' b, UpdateAtChild' b l v ( '(l',v')': r) r')
>  -- note that if pattern over r is not written this does not compile
>        => UpdateAtChild l v ( '(l',v') ': r) r' where
>   updateAtChild = updateAtChild' (Proxy :: Proxy b)


> instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
>          UpdateAtChild' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
>   updateAtChild' _ (l :: Label l) newattrib (attrib `ConsCh` attribs)
>     = (TaggedChAttr l newattrib) `ConsCh` attribs

>
> instance ( UpdateAtChild l v r r', LabelSet  ( a ': r' ) ) =>
>          UpdateAtChild' False l v (a ': r) (a ': r') where
>   updateAtChild' (b :: Proxy False) (l :: Label l) v
>     (ConsCh attrib xs :: ChAttsRec ( a ': r))
>     = case (updateAtChild l v xs) of
>         xs' -> ConsCh attrib xs' :: ChAttsRec (a ': r')

> instance Fail (FieldNotFound l) => UpdateAtChild l v '[] '[] where
>     updateAtChild _ _ r = r

>

%if True

Some tests
%endif

> infixr 2 .*
> (.*) :: LabelSet ('(ch, attrib) : attribs) =>
>   TaggedChAttr ch attrib -> ChAttsRec attribs -> ChAttsRec ('(ch, attrib) : attribs)
> (.*) = ConsCh

TODO: cambiar nombre de params aca

> {-
> infixr 4 =.
> (.=) :: Label l -> v -> Tagged l v
> (Label :: Label l) =. (v::v) = Tagged v :: Tagged l v
> -}

