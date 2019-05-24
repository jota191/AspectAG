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


Attribute grammars prove that they are not only useful to implement programming
languages, but also as a general purpose programming paradigm. Pitifully an
attribute grammar is an example of a structure that can be easily illformed. It
is a common mistake to try to use attributes that are not defined in some
production. This kind of error can be introduced directly, or by associating
rules to incorrect productions. Like showed in the prevoius section, \AspectAG
captures common errors. \AspectAG internals are built from strongly typed
heterogeneous records, so an incorrect lookup would be detected at compile time.

Detecting errors is not enough. It is a common problem when implementing
Embedded DSLs that implementation leaks on type errors. User defined type errors
[REF] a tool introduced to solve this issue. The family |GHC.TypeLits.TypeError|
can be used to print a custom error message but it is not clear how to structure
the implementation in a modular, dependable and scalable way. On section
\ref{sec:requirements} we present our solution.


\subsection{Extensible Records: Using Type Level Programming in Haskell}
In \AspectAG we use multiple instances of extensible records:

\begin{itemize}
\item
  |Attribution|s are mappings from attribute names to values.
\item
  For each production, there is a set of children, each one with an
associated attribution. Note that in this case
each field is not a flat value, but a full record by itself. This must be
reflected on types as our goal is to code strongly kinded.
\item
  \emph{Aspects} are a record of rules indexed by productions.
\item
  Semantic functions are kept on a record (not visible by the user).
\end{itemize}

\subsection{Polymorphic Heterogeneous Records}

Extensible records coded using type level programming are already part of the
folklore in the Haskell community. The {\tt HList}
library\cite{Kiselyov:2004:STH:1017472.1017488} popularized them. Old versions
of HList originally abused of Multi Parameter Typeclasses and Functional
Dependencies. Modern Haskell provides extensions to the type system to encode
this sort of dependent types in a better way. Notably {\tt
  TypeFamilies}\cite{Chakravarty:2005:ATC:1047659.1040306,
  Chakravarty:2005:ATS:1090189.1086397, Sulzmann:2007:SFT:1190315.1190324}, {\tt
  DataKinds}~\cite{Yorgey:2012:GHP:2103786.2103795} implementing data promotion.
{\tt PolyKinds} providing kind polymorphism, {\tt KindSignatures}\cite{ghcman}.


Other implementations such a Vinyl\cite{libvinyl} or CTRex\cite{libCTRex} have
been introduced. One common way to implement a |Record| is using a
|GADT|\cite{Cheney2003FirstClassPT,Xi:2003:GRD:604131.604150}. Usually
heterogeneous records contain values of kind |Type|. It makes sense since |Type|
is the kind of inhabited types and records store values. At kind level this is a
sort of untyped programming; datatype constructors take information with
expressive kinds and wrap it on a uniform box. In use cases such as children
records where we store an attribution we desire to state this on kinds. We
abstract this notion and code a library of a very polymporphic implementation of
extensible records as follows:


> data Rec (c :: k) (r :: [(k', k'')]) :: Type where
>   EmptyRec  ::  Rec c '[]
>   ConsRec   ::  LabelSet ( '(l,v) ': r)
>             =>  TagField c l v -> Rec c r
>             ->  Rec c ( '(l, v) ': r)


A record is indexed on a promoted list of pairs |r|. The kind of the first
component in each pair is polymorphic since it is not mandatory that the type of
labels is inhabited; they live only at type level. The second component is also
polymorphic and can be a rich kind. The |Tagfield| constructor solves the
problem of wrapping and unwrapping some value so that it actually stores
something with a |Type|. |LabelSet| is a predicate that encodes the fact that
there are no repeated labels. The parameter |c| is an extra index pointing out
wich instance of record are we defining. |TagField| is a fancier implementation
of the well known |Data.Tagged| datatype:

> data TagField (c :: k) (l :: k') (v :: k'') where
>   TagField  ::  Label c -> Label l -> WrapField c v
>             ->  TagField c l v

where labels are proxies

> data Label (l :: k) = Label

The |TagField| constructor uses |Label| arguments to build instances because we
usually have them avaiable at term level as we saw in the example of section
[REF], but type applications -or a much less elegant annotation- would work
fine. The third argument of type |WrapField c v| should be the value that we
want to tag. The type level term |v| is kind polymorphic, for instance a
contrete instance of |v| can be something like |[(Att, Type)]| in the case of
children. When actually creating a field to append in a record a real value must
be stored, all this kind information must be Wrapped by a type constructor. The
type family

> type family WrapField (c :: k) (v :: k') :: Type

computes depending on |c| the wrapping ov |v| under a suitable type constructor.
Note that if |v| is already inhabitated |WrapField c| can be the identity
function (and it actually is in every instance like that we have implemented).

We usually encode some of our functions as operators, for example, instead of
|ConsRec| we usually use an infix operator |(.*.)|.


Another relevant design decision is the implementation of the |LabelSet|
constraint. A similar class is introduced on the
HList\cite{Kiselyov:2004:STH:1017472.1017488} library. By using a type class to
encode a predicate new instances can be defined anytime since classes are open.
When an instance is not found, one could argue that does not mean that the
predicate is |False|, but that the typechecker did not find a proof. In the case
of |LabelSet| given a set of labels, once we know how to compare on their kind
|LabelSet| is closed and decidable. On previous iterations of our development we
used the constraint alternative and encoded instances of |TypeError| for cases
where a repeated label is found. We will use an unified way to process type
errors as whe shall see in section \ref{sec:requirements}. To do that we need to
manipulate truth value of the result, a Boolean type family seems the way to go:

> type family LabelSetF (r :: [(k, k')]) :: Bool where
>   LabelSetF '[]          = True
>   LabelSetF [(l, v)]     = True
>   LabelSetF ( '(l, v) ': '(l', v') ': r)
>    = And3  (Not (l == l')) 
>            (LabelSetF ( '(l, v)   ': r) )
>            (LabelSetF ( '(l', v') ': r) )

Then we encode the predicate version since it fits better in some contexts,
such as the |ConsRec| constructor.

> class LabelSet (r :: [(k, k')]) where {}
> instance LabelSetF r ~ True => LabelSet r


\subsection{Record Instances}

Most functions over records are implemented over the polykinded implementation.
Then we use this record library to implement our actual record-like data
structures. To introduce a record we must give an index acting as a name, and
implement the family instance |WrapField|. To print pretty and domain specific
error messages we also need to add instances for |ShowField| and |ShowRec|, as
we shall see later. We give some examples.

\subsubsection{Example: Attribution}\hfill\break

Attributions are mappings from attribute names to values. To make an index we
define a datatype as:

> data AttReco

On the definition of |GenRecord| the |c| parameter is polykinded. We use the
kind |Type| for indexes in our instances since |Type| is the only extensible
kind. Fixing the kind of this index the generic record library allows a closed
set of records.

Attributions are records using the |AttReco| index. Also, we define a
descriptive name and fix the polymorphic kinds since Attribution labels are of
kind |Att|, and fields of kind |Type|.

> type Attribution (attr :: [(Att, Type)]) = Rec AttReco attr

We do not need to actually wrap the fields since they are simply values:

> type instance  WrapField AttReco  (v :: Type) = v

We also use an specific name for fields:

> type Attribute (l :: Att) (v :: Type) = TagField AttReco l v
> type Attribute        = TagField AttReco


Pattern matching is a very useful feature in functional programming languages,
but somewhat incompatible with abstract datatypes. Hiding constructors
of |GenRecord| is nice but we lose pattern matching.
Fortunately Haskell implements pattern synonyms.

\todo{aparentemente hay bastante literatura con esto y los pattern synonyms son
  algo nuevo, tengo que buscar referencias}

For each instance of record we define fake constructors, specialized versions of
|TagField|, |EmptyRec| an |ConsAtt|. In the case of attributions this can be
coded as follows:

> pattern  Attribute     ::  v -> TagField AttReco l v
> pattern  Attribute v   =   TagField Label Label v
> pattern  EmptyAtt      ::  Attribution '[]
> pattern  EmptyAtt      =   EmptyRec
> pattern  ConsAtt       ::  LabelSet ( '(att, val) ': atts)
>                        =>  Attribute att val -> Attribution atts
>                        ->  Attribution ( '(att,val) ': atts)
> pattern  ConsAtt a as  =   ConsRec att atts





\subsubsection{Example: Children Records}\hfill\break

Again, lets build a new index:

> data ChiReco (prd :: Prod)

A child is associated to a production. Our instance has itself an index with
that information. Recall that |Prod| has a name, for the production but also a
name for the non-terminal that it rewrites, so all this information is contained
on a child and used to check well formedness where it is used.

> type ChAttsRec prd (chs :: [(Child,[(Att,Type)])])
>    = Rec (ChiReco prd) chs

|WrapField| in this case takes the type information of the field, which is
not inhabited, and puts the |Attribution| wrapper.

> type instance  WrapField (ChiReco prd)  (v :: [(Att, Type)])
>   = Attribution v

Again pattern synonyms are defined.



\todo{capaz figure tabla con los records y sus constructores?}


\subsection{Requirements}
\label{sec:requirements}
As a framework to program type errors we introduce the concept of
requirements.

> class Require (op   :: Type)
>               (ctx  :: [ErrorMessage])  where
>    type ReqR op :: k -- TODO:
>    req :: Proxy ctx -> op -> ReqR op

Given an operation |op|, that is actually a product where all the parameters of
the current requirement are passed, |req| extracts the tangible results whose
return type of type depend on the operation. This is very general and will be
more clear by introduce some examples. Each time we lookup in a record (for
example when accessing attributes) we require that some label actually belongs
to the record. If this requirement is not accomplished an error must be raised
at compile time. That means that there will be no regular instance of this class.
By program an special error instance we can capture type errors. The |Require|
class is so general to treat all type errors in a unified manner. By doing it
case by case it is difficult to track all cases and maintain them.

To print pretty type errors, we define a special operation:

> data OpError (m :: ErrorMessage) where {}

Which is a phantom type containing some useful information to print.
When we call |req| with this operator the type checker explodes since
there is only one instance:

> instance (TypeError (Text "Error: " :<>: m :$$:
>                      Text "from context: " :<>: ShowCTX ctx))
>   => Require (OpError m) ctx where {}





\begin{table}[t] 
   \label{tab:req}
   \small % text size of table content
   \centering % center the table
   \begin{tabular}{lcr} % alignment of each column data
   \toprule[\heavyrulewidth] \textbf{Operation} & \textbf{Requirement} &
   \textbf{Require Operator} \\ \midrule Record Lookup & label is a member &
   |OpLookup| \\ \hline Record Update & label is a member & |OpUpdate| \\ \hline
   Record Extension & label is not a member & |OpExtend| \\ \hline New
   synthesized attribute & {\begin{minipage}[t]{.3\linewidth}\begin{center}
         attribute type $\equiv$ \\type of definition \end{center}\end{minipage}}
   & |RequireEq| \\ \hline New inherited attribute &
   {\begin{minipage}[t]{.3\linewidth}\begin{center} attribute type $\equiv$ \\type
         of definition \end{center}\end{minipage}}& |RequireEq| \\ \hline
   New inherited
   attribute & {\begin{minipage}[t]{.3\linewidth}\begin{center}
         argument production \\$\equiv$ child production
   \end{center}\end{minipage}}& |RequireEq|
   \\ \bottomrule[\heavyrulewidth]
   \end{tabular}
   \caption{Example Requirements}
\end{table}


A call to |OpError| happens when some requirement is not fullfilled. Some
examples of requirements implemented in our library are shown on table
~\ref{tab:req}:






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


|ShowRec| and |ShowField| are type families used to print correctly the type
 information depending on which category of records we are working on.

> type family ShowRec    (c :: k)    :: Symbol
> type family ShowField  (c :: k)  :: Symbol

For example, for attributions we implement

> type instance ShowRec AttReco
>   = "Attribution"
> type instance ShowField AttReco
>   = "attribute named "

For children:

> type instance ShowRec (ChiReco a)
>   = "Children Map"
> type instance ShowField (ChiReco a)
>   = "child labelled "


The fact that type families can be defined open is very convenient in this
context. We argue that our generic records and/or the require framework are a
useful libraries by their own.

The |ShowT| family is even more interesting.

> type family ShowT (t :: k) :: ErrorMessage

When we print labels which are types with kinds such as |Att|, |Prd|, |Chi| and
so on, to show clear type errors we want to print them in a different way
depending on the case, formatting the information correctly. At term level a
fully polymorphic function cannot touch its arguments. Type classes are the way
to define bounded parametricity. We do not have kind classes but they are not
necessary since polykinded type families are actually not parametric. At type
level we can actually inspect kinds. Therefore, the following definitions are
completely legal:

> type instance  ShowT ('Att l t)
>   =     Text  "Attribute "  :<>: Text l
>   :<>:  Text  ":"           :<>: ShowT t
> type instance  ShowT ('Prd l nt)
>   =     ShowT nt :<>: Text "::Production "
>   :<>:  Text l
> type instance  ShowT ('Chi l p s)
>   =     ShowT p   :<>:  Text "::Child " :<>: Text l
>   :<>:  Text ":"  :<>:  ShowT s
> type instance  ShowT ('Left l)
>   = ShowT l
> type instance  ShowT ('Right r)
>   = ShowT r
> type instance  ShowT ('NT l)
>   = Text "Non-Terminal " :<>: Text l
> type instance  ShowT ('T  l)
>   = Text "Terminal " :<>: ShowT l



Also, we can code an instance for any type of kind |Type|:

> type instance ShowT (t :: Type)
>   = ShowType t

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
