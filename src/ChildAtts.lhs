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

> data LabelCh :: (k,Type) -> Type where
>   LabelCh :: LabelCh '(k,Type)

> nameChi :: LabelCh '(k,t) -> Label k
> nameChi _ = Label

> type family TypeChi l where
>   TypeChi (LabelCh '(k,t)) = t

> data TaggedChAttr (l::(k,Type)) (v :: [(k,Type)]) :: Type where
>   TaggedChAttr :: LabelCh l -> Attribution v -> TaggedChAttr l v
> unTaggedChAttr :: TaggedChAttr l v -> Attribution v
> unTaggedChAttr (TaggedChAttr _ v) = v

> data TaggedChAtt :: ((k,Type),Type) -> Type where
>   TaggedChAtt :: LabelCh '(l,t) -> v -> TaggedChAtt '( '(l,t) ,v)
> unTaggedChAtt :: TaggedChAtt '( '(l,t), v) -> v
> unTaggedChAtt (TaggedChAtt _ v) = v
> labelTChAtt :: TaggedChAtt '( '(k,Type),v) -> LabelCh '(k,Type)
> labelTChAtt _ = LabelCh


> -- the record of attribution fot the children
> data ChAttsRec :: [((k,Type) , [(k,Type)])] -> Type where
>   EmptyCh :: ChAttsRec '[]
>   ConsCh  :: LabelSet ( '( '(l,t), v) ': xs) =>
>    TaggedChAttr '(l,t) v -> ChAttsRec xs -> ChAttsRec ( '( '(l,t),v) ': xs)


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

> class HasChild (l:: (k,Type))
>    (r :: [((k,Type) ,[(k,Type)])]) v | l r -> v where
>    hLookupByChild:: LabelCh l -> ChAttsRec r -> Attribution v

> instance (HEqK l l1 b, HasChild' b l ( '(l1,v1) ': r) v)
>     => HasChild l ( '(l1,v1) ': r) v where
>     hLookupByChild l (r :: ChAttsRec ( '(l1,v1) ': r)) =
>          hLookupByChild' (Proxy::Proxy b) l r


> class HasChild' (b::Bool) (l :: (k,Type)) (r::[((k,Type),[(k,Type)])]) v
>   | b l r -> v where
>     hLookupByChild':: Proxy b -> LabelCh l -> ChAttsRec r -> Attribution v

> instance HasChild' True l ( '(l,v) ': r) v where
>    hLookupByChild' _ _ (ConsCh lv _) = unTaggedChAttr lv
> instance HasChild l r v => HasChild' False l ( '(l2,v2) ': r) v where
>    hLookupByChild' _ l (ConsCh _ r) = hLookupByChild l r
 


UPDATEATLABEL

> class UpdateAtChild (l :: (k,Type)) (v :: [(k,Type)])
>       (r :: [((k,Type),[(k,Type)])])(r' :: [((k,Type),[(k,Type)])])
>    | l v r -> r' where
>   updateAtChild :: LabelCh l -> Attribution v -> ChAttsRec r -> ChAttsRec r'

So we need an auxiliary class with an extra parameter to decide if we update
on the head of r or not

> class UpdateAtChild' (b::Bool)(l::(k,Type))(v::[(k,Type)])
>       (r::[((k,Type),[(k,Type)])])(r'::[((k,Type),[(k,Type)])])
>     | b l v r -> r'  where
>   updateAtChild' ::
>    Proxy b -> LabelCh l -> Attribution v -> ChAttsRec r -> ChAttsRec r'



> instance (HEqK l l' b, UpdateAtChild' b l v ( '(l',v')': r) r')
>  -- note that if pattern over r is not written this does not compile
>        => UpdateAtChild l v ( '(l',v') ': r) r' where
>   updateAtChild = updateAtChild' (Proxy :: Proxy b)


> instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
>          UpdateAtChild' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
>   updateAtChild' _ (l :: LabelCh l) newattrib (attrib `ConsCh` attribs)
>     = (TaggedChAttr l newattrib) `ConsCh` attribs

>
> instance ( UpdateAtChild l v r r', LabelSet  ( a ': r' ) ) =>
>          UpdateAtChild' False l v (a ': r) (a ': r') where
>   updateAtChild' (b :: Proxy False) (l :: LabelCh l) v
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
> (.*) :: LabelSet ('( '(ch,t), attrib) : attribs) =>
>   TaggedChAttr '(ch,t) attrib -> ChAttsRec attribs
>   -> ChAttsRec ('( '(ch,t), attrib) : attribs)
> (.*) = ConsCh

TODO: cambiar nombre de params aca

> {-
> infixr 4 =.
> (.=) :: Label l -> v -> Tagged l v
> (Label :: Label l) =. (v::v) = Tagged v :: Tagged l v
> -}

