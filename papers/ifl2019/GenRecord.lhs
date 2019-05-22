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

> class Require (op   :: Type)
>               (ctx  :: [ErrorMessage])  where
>    type ReqR op :: k
>    req :: Proxy ctx -> op -> ReqR op

%if False



data OpLookup (c :: Type)
              (l  :: k)
              (r  :: [(k, k')]) :: Type where
  OpLookup :: Label l -> Rec c r -> OpLookup c l r

data OpLookup' (b  :: Bool)
               (c  :: Type)
               (l  :: k)
               (r  :: [(k, k')]) :: Type where
  OpLookup' :: Proxy b -> Label l -> Rec c r -> OpLookup' b c l r




instance (Require (OpLookup' (l == l') c l ( '(l', v) ': r)) ctx)
  => Require (OpLookup c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup c l ( '(l', v) ': r))
    = ReqR (OpLookup' (l == l') c l ( '(l', v) ': r))
  req ctx (OpLookup l r) = req ctx (OpLookup' (Proxy @ (l == l')) l r)

instance Require (OpLookup' 'True c l ( '(l, v) ': r)) ctx where
  type ReqR (OpLookup' 'True c l ( '(l, v) ': r)) = WrapField c v
  req Proxy (OpLookup' Proxy Label (ConsRec f _)) = untagField f

instance (Require (OpLookup c l r) ctx)
  => Require (OpLookup' False c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup' False c l ( '(l', v) ': r)) = ReqR (OpLookup c l r)
  req ctx (OpLookup' Proxy l (ConsRec _ r)) = req ctx (OpLookup l r)




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
