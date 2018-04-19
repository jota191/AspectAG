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



%if True

Some tests

> 
> data Label1; data Label2; data Label3;data Label4
> label1 = Label :: Label Label1
> label2 = Label :: Label Label2
> label3 = Label :: Label Label3
> label4 = Label :: Label Label4
> tagged1 = Tagged 3   :: Tagged Label1 Int 
> tagged2 = Tagged '4' :: Tagged Label2 Char
> tagged3 = Tagged '4' :: Tagged Label3 Char

> record1 = ConsR tagged2 EmptyR
> -- test2 = ConsR att2 test1 does not compile because of label duplication
> record2 = ConsR tagged1 record1
> record3 = ConsR tagged3 record2
> 


> --test_update_1 = updateAtLabelRec label4 False record3 --should fail
> test_update_2 = updateAtLabelRec label2 False record3 
> test_update_3 = updateAtLabelRec label2 "hola" record3
> test_update_4 = updateAtLabelRec label2 '9' record3 
> test_update_5 = updateAtLabelRec label3 "hola" record3 
> test_update_6 = updateAtLabelRec label3 '9' record3 

%endif

> infixr 2 *.
> (*.) :: LabelSet ('(att, val) : atts) =>
>     Tagged att val -> Record atts -> Record ('(att, val) : atts)
> (*.) = ConsR

TODO: cambiar nombre de params aca

> infixr 4 =.
> (=.) :: Label l -> v -> Tagged l v
> (Label :: Label l) =. (v::v) = Tagged v :: Tagged l v
