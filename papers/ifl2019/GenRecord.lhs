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
>              TypeFamilies,
>              InstanceSigs,
>              AllowAmbiguousTypes,
>              TypeApplications,
>              PatternSynonyms
> #-}


%endif

\todo{references, HList, vinyl, etc}

\subsection{Extensible Records: Using Type Level Programming in Haskell}


In our implementation we use extensible records in more than one place.
\begin{itemize}
\item
  |Attribution|s are mappings from attribute names to values.
\item
  For each production, there is a set of children, each one with an
associated attribution. This is modelled as a record. Note that in this case
each field is not a flat value, but a full record by itself. This must be
reflected on types as our goal is to code strongly kinded.
\item
  \todo{}
\end{itemize}


Modern Haskell provides extensions to the type system that allows to encode
this sort of dependent types.
Notably {\tt TypeFamilies}\cite{Chakravarty:2005:ATC:1047659.1040306,
 Chakravarty:2005:ATS:1090189.1086397, Sulzmann:2007:SFT:1190315.1190324}, {\tt
  DataKinds}~\cite{Yorgey:2012:GHP:2103786.2103795} implementing data promotion.
 {\tt PolyKinds} providing kind polymorphism, {\tt KindSignatures}\cite{ghcman} permite. Or {\tt GADTs}\cite{Cheney2003FirstClassPT,Xi:2003:GRD:604131.604150}.

> data Record (r :: [(k, Type)]) :: Type where
>   EmptyRec  ::  Record '[]
>   ConsRec   ::  LabelSet ( '(l,v) ': r)
>             =>  Tagged l v -> Record r
>             -> Record ( '(l, v) ': r)

A data type isomorphic to the previous one would model well some of the
structures in our library, for example attributions. To model children
in a strongly kinded manner it is not enough. To say that every field
is actually an attribution we may implement a predicate (as a type class)
wich degenerates to an old fashioned type level programming with constraints,
a la prolog.

We prefer to introduce something like another specialized record with a
declaration like

< data ChAttsRec (r :: [([k, (k', Type)])]) :: Type where ..

But of course, we do not want to implement every structure each time.

\subsection{Generic Records}

We develop a parametrized implementation, as follows:

> data Rec (c :: k) (r :: [(k', k'')]) :: Type where
>   EmptyRec  ::  Rec c '[]
>   ConsRec   ::  LabelSet ( '(l,v) ': r)
>             =>  TagField c l v -> Rec c r
>             -> Rec c ( '(l, v) ': r)

The parameter |c| is an extra index defining wich category of record
are we defining. |TagField| is a fancy implementation of the well known
|Tagged| data type, as we shall see.

\todo{\lipsum}

> type family LabelSetF (r :: [(k, k')]) :: Bool where
>   LabelSetF '[]          = True
>   LabelSetF [(l, v)]     = True
>   LabelSetF ( '(l, v) ': '(l', v') ': r)
>    = And3  (Not (l == l')) 
>            (LabelSetF ( '(l, v)   ': r) )
>            (LabelSetF ( '(l', v') ': r) )

> class LabelSet (r :: [(k, k')]) where {}
> instance LabelSetF r ~ True => LabelSet r


\todo{\lipsum}

> data TagField (c :: k) (l :: k') (v :: k'') where
>   TagField  ::  Label c -> Label l -> WrapField c v
>             ->  TagField c l v
> data Label (l :: k) = Label

\todo{\lipsum}

> type family WrapField (c :: k')  (v :: k) :: Type

> infixr 2 .*.
> (.*.) :: LabelSet ( '(l, v) ': r) =>
>     TagField c l v -> Rec c r -> Rec c ( '(l,v) ': r)
> (.*.) = ConsRec


\subsection{Record Instances}

\todo{\lipsum}

\subsubsection{Example: Attribution}\hfill\break

> type Attribution   = Rec AttReco

> data AttReco

> type instance  WrapField AttReco  (v :: Type) = v



> type Attribute        = TagField AttReco
> pattern Attribute :: v -> TagField AttReco l v
> pattern Attribute v = TagField Label Label v

> pattern EmptyAtt :: Attribution '[]
> pattern EmptyAtt = EmptyRec
> pattern ConsAtt :: LabelSet ( '(att, val) ': atts)
>     =>  Attribute att val -> Attribution atts
>     ->  Attribution ( '(att,val) ': atts)
> pattern ConsAtt att atts = ConsRec att atts

\subsubsection{Example: Children Records}\hfill\break


> type ChAttsRec prd (chs :: [(Child,[(Att,Type)])])
>    = Rec (ChiReco prd) chs

> data ChiReco (prd :: Prod)

> type instance  WrapField (ChiReco prd)  (v :: [(k, Type)])
>   = Attribution v



\subsection{Requirements}

As a framework to program type errors we introduce the concept of
requirements.

> class Require (op   :: Type)
>               (ctx  :: [ErrorMessage])  where
>    type ReqR op :: k -- TODO: ver si era necesario este polimorfismo
>    req :: Proxy ctx -> op -> ReqR op

Given an operation |op|, that is actually a product where all the parameters of
the current require are passed, |req| extracts the tangible results (of type
depending on the operation). This is very general and will be more clear by
introduce some examples. Each time we lookup in a record (for example when
accessing attributes) we require that some label actually belongs to the record.
If this requirement is not accomplished an error must be raised at compile time.
That means that there will be no good instance of this class. By program an
special error instance we can capture type errors. The |Require| class is so
general to treat all type errors in a unified manner. By doing it case by case
it is difficult to track all cases and maintain them.

For example, we define the lookup operator:

> data OpLookup  (c  :: Type)
>                (l  :: k)
>                (r  :: [(k, k')]) :: Type where
>   OpLookup  ::  Label l -> Rec c r
>             ->  OpLookup c l r

which is an algebraic datatype containing the record category, a label which is
the index we are looking for, and the record parameter. To lookup on a record we
need to code a dependant type function, which is encoded in Haskell with the
usual idioms of type level programming. We need to inspect the head label and
decide to return the value contained or call the lookup function recursively
depending on the types. Moreover, the proof of equality must be explicit.

We introduce a new |OpLookup'| with an auxiliar |Bool| at type level:

> data OpLookup'  (b  :: Bool)
>                 (c  :: Type)
>                 (l  :: k)
>                 (r  :: [(k, k')]) :: Type where
>   OpLookup'  ::  Proxy b -> Label l -> Rec c r
>              ->  OpLookup' b c l r


and then we can implement our dependent function. For |OpLookup| we take the head
label |l'| and use the auxiliar function with the value equal to the predicate of
equality of |l'| and the argument label |l|:

> instance (Require (OpLookup' (l == l') c l ( '(l', v) ': r)) ctx)
>   =>  Require (OpLookup c l ( '(l', v) ': r)) ctx                  where
>   type ReqR (OpLookup c l ( '(l', v) ': r))
>     = ReqR (OpLookup' (l == l') c l ( '(l', v) ': r))
>   req ctx (OpLookup l r)
>     = req ctx (OpLookup' (Proxy @ (l == l')) l r)

To implement instances for |OpLookup'| is easy. The true case corresponds to
a |head| function since we know that the searched label is on head:

> instance Require (OpLookup' 'True c l ( '(l, v) ': r)) ctx where
>   type ReqR (OpLookup' 'True c l ( '(l, v) ': r))
>     = WrapField c v
>   req Proxy (OpLookup' Proxy Label (ConsRec f _))
>     = untagField f

The false case corresponds to a call of |OpLookup| on tail:

> instance (Require (OpLookup c l r) ctx)
>   => Require (OpLookup' False c l ( '(l', v) ': r)) ctx where
>   type ReqR (OpLookup' False c l ( '(l', v) ': r))
>     = ReqR (OpLookup c l r)
>   req ctx (OpLookup' Proxy l (ConsRec _ r))
>     = req ctx (OpLookup l r)


When we lookup on an empty record an error happened: There is no value
tagged with the searched label.

To print pretty type errors, we define a special operation:

> data OpError (m :: ErrorMessage) where {}

Which is a phantom type containing some useful information to print.
When we call |req| with this operator the type checker explodes since
there is only one instance:

> instance (TypeError (Text "Error: " :<>: m :$$:
>                      Text "from context: " :<>: ShowCTX ctx))
>   => Require (OpError m) ctx where {}

Recall thet |TypeError| and |ErrorMessage| are defined in |GHC.TypeLits|. The
type family |TypeError| is like the function |error| but at type level. When it
is 'called' a type error is raised. |TypeError| is so polymorphic that we can
use it as a Constraint, like in this case. This generic instance is used to
print all sort of type errors in a unified way, but the specific information of
what happened is on |OpError| which is built from a specific instance of
|OpLookup|:

> instance Require (OpError
>     (     Text "field not Found on "  :<>: Text (ShowRec c)
>     :$$:  Text "looking up the "      :<>: Text (ShowField c)
>     :<>:  ShowT l )) ctx
>   => Require  (OpLookup c l ( '[]  :: [(k, k')])) ctx where
>   type ReqR   (OpLookup c l ('[]   :: [(k, k')])  ) = ()
>   req = undefined


This procedure was used in all our development:
\begin{itemize}
\item Code dependent Haskell, if everything goes well we neither
  access bad indexes nor use rules for incorrect productions, etc.

\item Encode the bad cases, requiring an |OpError|. Note that when building it,
  like in the former |Require| instance for |OpLookup| a lot of information
  about types is on scope and can be used to print an informative error.
\end{itemize}




%if False

instance
  Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                     :$$: Text "looking up the " :<>: Text (ShowField c)
                           :<>: ShowT l
                          )) ctx
  => Require (OpLookup c l ( '[] :: [(k,k')])) ctx where
  type ReqR (OpLookup c l ('[] :: [(k,k')])  ) = ()
  req = undefined

type family ShowRec c :: Symbol

type family ShowField c :: Symbol

instance (Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                    :$$: Text "updating the " :<>: Text (ShowField c)
                     :<>: ShowT l)) ctx)
  => Require (OpUpdate c l v '[]) ctx where 
  type ReqR (OpUpdate c l v ('[] )  ) = '[]
  req = undefined

-- | update
data OpUpdate (c  :: Type)
              (l  :: k)
              (v  :: k')
              (r  :: [(k, k')]) :: Type where
  OpUpdate :: Label l -> WrapField c v -> Rec c r
           -> OpUpdate c l v r

data OpUpdate' (b  :: Bool)
               (c  :: Type)
               (l  :: k)
               (v  :: k')
               (r  :: [(k, k')]) :: Type where
  OpUpdate' :: Proxy p -> Label l -> WrapField c v ->  Rec c r
           -> OpUpdate' b c l v r


instance (Require (OpUpdate' (l == l') c l v ( '(l', v') ': r) ) ctx )
  => Require (OpUpdate c l v ( '(l', v') ': r) ) ctx where
  type ReqR (OpUpdate c l v ( '(l', v') ': r) )
    = ReqR (OpUpdate' (l == l') c l v ( '(l', v') ': r) )
  req ctx (OpUpdate l f r)
    = (req @(OpUpdate' (l == l') _ _ v _ ))
       ctx (OpUpdate' (Proxy @(l == l')) l f r)


instance ( LabelSet ( '(l, v) ': r)
         , LabelSet ( '(l, v') ': r))
  => Require (OpUpdate' 'True c l v ( '(l, v') ': r)) ctx where
  type ReqR (OpUpdate' 'True c l v ( '(l, v') ': r))
    = Rec c ( '(l, v) ': r)
  req ctx (OpUpdate' proxy label field (ConsRec tgf r))
    = ConsRec (TagField Label label field) r


instance ( Require (OpUpdate c l v r) ctx
         , UnWrap (ReqR (OpUpdate c l v r)) ~ r0
         , LabelSet ( '(l', v') : r0)
         , ReqR (OpUpdate c l v r) ~ Rec c r0)
  => Require (OpUpdate' 'False c l v ( '(l',v') ': r)) ctx where
  type ReqR (OpUpdate' 'False c l v ( '(l',v') ': r))
    = Rec c ( '(l',v') ': (UnWrap (ReqR (OpUpdate c l v r))))
  req ctx (OpUpdate' _ l f (ConsRec field r))
    = ConsRec field $ (req @(OpUpdate _ _ v r)) ctx (OpUpdate l f r)



type family UnWrap t :: [(k,k')]
type instance UnWrap (Rec c r) = r




data OpExtend (c :: Type)
              (l  :: k)
              (v  :: k')
              (r  :: [(k, k')]) :: Type where
  OpExtend :: Label l -> WrapField c v -> Rec c r
           -> OpExtend c l v r

data OpExtend' (b :: Bool)
               (c :: Type)
               (l  :: k)
               (v  :: k')
               (r  :: [(k, k')]) :: Type where
  OpExtend' :: Proxy b -> Label l -> WrapField c v -> Rec c r
           -> OpExtend' b c l v r


instance (LabelSetF ( '(l, v) ': r) ~ 'True)
  => Require (OpExtend' True  c l v r) ctx where
  type ReqR (OpExtend' True c l v r) = Rec c ( '(l, v) ': r)
  req ctx (OpExtend' _ l f r) = ConsRec (TagField (Label @c) l f) r


instance ( LabelSetF ( '(l, v) ':  r) ~ b
         , Require (OpExtend' b c l v r) ctx)
  => Require (OpExtend c l v r) ctx where
  type ReqR (OpExtend c l v r)
    = ReqR (OpExtend' (LabelSetF ( '(l, v) ': r)) c l v r)
  req ctx (OpExtend l v r)
    = req @(OpExtend' (LabelSetF ( '(l, v) ': r)) _ _ v _ )
      ctx (OpExtend' Proxy l v r) 

instance Require (OpError (Text "Duplicated Labels on " :<>: Text (ShowRec c)
                          :$$: Text "on the " :<>: Text (ShowField c)
                           :<>: ShowT l
                          )) ctx
  => Require (OpExtend' False c l v (r :: [(k, k')])) ctx where
  type ReqR (OpExtend' False c l v r) = Rec c (r :: [(k, k')])
  req ctx (OpExtend' p l v r) = undefined



%endif
