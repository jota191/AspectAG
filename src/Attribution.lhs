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

> import Data.Kind 
> import Data.Type.Equality
> import Data.Proxy
> import Errors
> import Eq
> import Attribute

%endif

An attribution will be a map from attribute names to attribute values,
where names are labels purely phantom.
So we must code strongly type heterogeneous records.

TODO:

\begin{itemize}
  \item  explain why Attribution and not Record
  \item  explain why a fresh implementation instead of doing it over lists
\end{itemize}

Since attributions must be a map, we must ensure that
instances doesn't repeat labels. This kind of predicate can be encoded
by typeclasses, and encoded doing a sort of logic programming.
While we prefer a Functional style in this implementation, using more recent
extensions to ghc like typefamilies and dataKinds, instead of the old fashioned
logic style of type level programming, for tasks like this, where we implement
predicates, it makes more sense to do it this way.

LabelSet is a monoparameter typeclass, working as a predicate
over a promoted list of pairs, where first elements are the labels. {\tt l} is
an instance of {\tt LabelSet} when no labels are repeated.


REFERENCE TO EQ MODUELE

%if False

> class LabelSet (l :: [(k,Type)])
> instance LabelSet '[] -- empty set
> instance LabelSet '[ '(x,v)] -- singleton set

> instance ( HEqK l1 l2 leq
>          , LabelSet' '(l1,v1) '(l2,v2) leq r)
>         => LabelSet ( '(l1,v1) ': '(l2,v2) ': r)

> class LabelSet' l1v1 l2v2 (leq::Bool) r
> instance ( LabelSet ( '(l2,v2) ': r)
>          , LabelSet ( '(l1,v1) ': r)
>          ) => LabelSet' '(l1,v1) '(l2,v2) False r

> instance ( Fail (DuplicatedLabel l1) ) => LabelSet' l1 l2 True r

%endif

TODO: explain how the selection of the instance is done

We are ready to define Attributions.

> data Attribution :: forall k . [(k,Type)] -> Type where
>   EmptyAtt :: Attribution '[]
>   ConsAtt  :: -- LabelSet ( '(att, val) ': atts) =>
>    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
                                                  


%if False
Some boilerplate to show Attributes and Attributions

> instance Show (Attribution '[]) where
>   show _ = "«»"

> instance (Show val, Show (Attribution atts)) =>
>          Show (Attribution  ( '(att,val) ': atts ) ) where
>   show (ConsAtt att atts) = let tail = show atts
>                             in "«" ++ show (getVal att) ++ "," ++ drop 1 tail 

%endif


%if False

Some tests:
TODO: move this..

> data Label1; data Label2; data Label3;data Label4
> label1 = Label :: Label Label1
> label2 = Label :: Label Label2
> label3 = Label :: Label Label3
> label4 = Label :: Label Label4
> att1 = Attribute 3   :: Attribute Label1 Int 
> att2 = Attribute '4' :: Attribute Label2 Char
> att3 = Attribute '4' :: Attribute Label3 Char

> attrib1 = ConsAtt att2 EmptyAtt
> -- test2 = ConsAtt att2 test1 does not compile because of label duplication
> attrib2 = ConsAtt att1 attrib1
> attrib3 = ConsAtt att3 attrib2


test2 = (Proxy :: Proxy 'True ,True) .*. (Proxy :: Proxy 'False,'r') .*. EmptyR
  :: HRecord '[ '( 'True ,Bool), '( 'False ,Char)]


%endif


--- HasField

> class HasField (l::k) (r :: [(k,Type)]) v | l r -> v where
>    hLookupByLabel:: Label l -> Attribution r -> v

> instance (HEqK l l1 b, HasField' b l ( '(l1,v1) ': r) v)
>     => HasField l ( '(l1,v1) ': r) v where
>     hLookupByLabel l (r :: Attribution ( '(l1,v1) ': r)) =
>          hLookupByLabel' (Proxy::Proxy b) l r

> 
> class HasField' (b::Bool) (l :: k) (r::[(k,Type)]) v | b l r -> v where
>     hLookupByLabel':: Proxy b -> Label l -> Attribution r -> v

> instance HasField' True l ( '(l,v) ': r) v where
>    hLookupByLabel' _ _ (ConsAtt (Attribute v) _) = v
> instance HasField l r v => HasField' False l ( '(l2,v2) ': r) v where
>    hLookupByLabel' _ l (ConsAtt _ r) = hLookupByLabel l r
 

UpdateAtLabel

I attempt to code an indexed type implementation, where the resulting Type
function of the parameters.
I could code the type function over the type level,
the problem is when I do this on a type class to code ter level computations.
Since we decide from the context (HEqK ) the returned boolean must be a
parameter of UpdateAtLabelR, but since it's purely on the context,
it is free on the RHS...
I keep the code here, after the long comment the actual implementation starts

> {-
> class UpdateAtLabel (l :: k) (v :: Type) (r :: [(k,Type)]) where
>   type UpdateAtLabelR l v r :: [(k,Type)]
>   updateAtLabel :: Label l -> v -> Attribution r
>                 -> Attribution (UpdateAtLabelR l v r)

> instance (HEqK b l l', UpdateAtLabel' b l v r) => UpdateAtLabel l v r where
>   type UpdateAtLabelR l v r = UpdateAtLabelR' b l v r
>   updateAtLabel = undefined


> class UpdateAtLabel' (b::Bool) (l :: k) (v :: Type) (r :: [(k,Type)]) where
>   type UpdateAtLabelR' b l v r :: [(k,Type)]
>   updateAtLabel' :: Proxy b -> Label l -> v -> Attribution r
>                  -> Attribution (UpdateAtLabelR l v r)

> instance UpdateAtLabel l v '[ '(l',v' )] where
>   type UpdateAtLabelR l v '[ '(l,v' )] = '[ '(l,v)]
>   updateAtLabel Label v (ConsAtt _ EmptyAtt) = ConsAtt (Attribute v) EmptyAtt

> type family If (cond:: Bool) (thn :: k) (els :: k) :: k where
>   If 'True  thn els = thn
>   If 'False thn els = els
> 
> type family Update (l :: k)(v :: Type)(r :: [(k,Type)]) :: [(k,Type)] where
>   Update l v ( '(l',v') ': xs ) = If (l == l') ( '(l, v) ': xs)
>                                                ( '(l',v') ': Update l v xs)

> class Up (b::Bool)(l :: k) (v :: Type) (r :: [(k,Type)]) where
>   up :: Proxy b -> Label l -> v -> Attribution r
>      -> Attribution (Update l v r)

> instance ((l == l') ~ 'True,
>          LabelSet ( '(l, v) ': xs))
>   => Up 'True l v ( '(l',v') ': xs) where
>               up _ l v (ConsAtt _ xs) = ConsAtt (Attribute v) xs

> instance ((l == l') ~ 'False,
>          LabelSet ( '(l, v) ': xs),
>          Up b l v xs)
>   => Up 'False l v ( '(l',v') ': xs) where
>               up _ l v (ConsAtt att xs)
>                 = ConsAtt att (up (Proxy::Proxy b) l v xs)
>

> instance (HEqK l l' False, UpdateAtLabel l v atts)
>     => UpdateAtLabel' False l v ( '(l',v') ': atts) where
>    type UpdateAtLabelR' False l v ( '(l',v') ': atts)
>                      = '(l',v') ': (UpdateAtLabelR l v atts) 
>    updateAtLabel' b l v (ConsAtt att atts)
>       = ConsAtt att ((updateAtLabel l v atts))
> -}


The fundep implementation is needed..

> class UpdateAtLabel (l :: k)(v :: Type)(r :: [(k,Type)])(r' :: [(k,Type)])
>    | l v r -> r' where
>   updateAtLabel :: Label l -> v -> Attribution r -> Attribution r'

So we need an auxiliary class with an extra parameter to decide if we update
on the head of r or not

> class UpdateAtLabel' (b::Bool)(l::k)(v::Type)(r::[(k,Type)])(r'::[(k,Type)])
>     | b l v r -> r'  where
>   updateAtLabel' :: Proxy b -> Label l -> v -> Attribution r -> Attribution r'



> instance (HEqK l l' b, UpdateAtLabel' b l v ( '(l',v')': r) r')
>  -- note that if pattern over r is not written this does not compile
>        => UpdateAtLabel l v ( '(l',v') ': r) r' where
>   updateAtLabel = updateAtLabel' (Proxy :: Proxy b)


> instance --(LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r)) =>
>          UpdateAtLabel' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
>   updateAtLabel' _ (l :: Label l) v (att `ConsAtt` atts)
>     = (Attribute v :: Attribute l v) `ConsAtt` atts

> 
> instance ( UpdateAtLabel l v r r') =>
>          UpdateAtLabel' False l v ( a ': r) ( a ': r') where
>   updateAtLabel' (b :: Proxy False) (l :: Label l) (v :: v)
>     (ConsAtt att xs :: Attribution ( a ': r))
>     = case (updateAtLabel l v xs) of
>         xs' -> ConsAtt att xs' :: Attribution( a ': r')

> instance Fail (FieldNotFound l) => UpdateAtLabel l v '[] '[] where
>     updateAtLabel _ _ r = r



%if True

Some tests

> --test_update_1 = updateAtLabel label4 False attrib3 --should fail
> test_update_2 = updateAtLabel label2 False attrib3 --should fail
> test_update_3 = updateAtLabel label2 "hola" attrib3 --should fail
> test_update_4 = updateAtLabel label2 '9' attrib3 --should fail
> test_update_5 = updateAtLabel label3 "hola" attrib3 --should fail
> test_update_6 = updateAtLabel label3 '9' attrib3 --should fail

%endif
