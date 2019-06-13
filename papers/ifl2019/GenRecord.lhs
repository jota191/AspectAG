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


% In this section we present the design of the new \AspectAG.
\label{sec:records}
In order to provide flexibility and safety, \AspectAG\ internals are built from
strongly typed extensible records. Then, mistakes like trying to access to an
undefined attribute or child are detected at compile time as an incorrect lookup
into a given record. Also, the definition of duplicated attributes results in a
type error, due to an incorrect record extension.

However, detecting errors is not enough.
If the error messages are difficult to understand and do not point to their possible sources,
using the library becomes a painful task.
It is a common problem when implementing
EDSLs using type-level programming that when a type error occurs, implementation details are leaked on error messages,
and this was the case of the previous version of \AspectAG.

As we have shown in the previous section, the library now captures common errors
and prints them in a readable way. We use user defined type errors; a tool
introduced in GHC to help improving the quality of type-level programming error
messages. The family |GHC.TypeLits.TypeError| can be used to print a custom
error message but it is not clear how to structure the implementation in a
modular, dependable and scalable way.

In the rest of this section we will show an
extensible records implementation and introduce a framework
to encode EDSL type errors.
%On section \ref{sec:requirements} we present our solution.


\subsection{Polymorphic Heterogeneous Records}
We use multiple instances of extensible records:

\begin{itemize}
\item
  |Attribution|s are mappings from attribute names to values.
\item
  For each production, there is a set of children, each one with an associated
  attribution. Note that in this case each field is not a flat value, but a full
  record by itself. It would be nice to reflect it on types.
\item
  \emph{Aspects} are records of rules indexed by productions.
\item
  Semantic functions are kept on a record (not visible by the user).
\end{itemize}

Extensible records coded using type-level programming are already part of the
folklore in the Haskell community. The {\tt HList}
library\cite{Kiselyov:2004:STH:1017472.1017488} popularized them. Old versions
of {\tt HList} originally abused of Multi Parameter
Typeclasses\cite{type-classes-an-exploration-of-the-design-space} and Functional
Dependencies\cite{DBLP:conf/esop/Jones00} to do the job. Modern GHC Haskell
provides extensions to the type system to support the encoding of this and more
sort-of dependent types in a more comfortable way. Notably {\tt
  TypeFamilies}\cite{Chakravarty:2005:ATC:1047659.1040306,
  Chakravarty:2005:ATS:1090189.1086397, Sulzmann:2007:SFT:1190315.1190324}, to
define functions at type-level, {\tt
  DataKinds}~\cite{Yorgey:2012:GHP:2103786.2103795}, implementing data
promotion, {\tt PolyKinds} providing kind polymorphism, {\tt
  KindSignatures}\cite{ghcman} to document and deambiguate kinds, or \break
{\tt TypeApplications}\cite{conf/esop/EisenbergWA16} to provide visible type
application. 

Other implementations of Extensible Records such as Vinyl\cite{libvinyl} or
CTRex\cite{libCTRex} have been introduced. One common way to implement a
|Record| is using a
|GADT|\cite{Cheney2003FirstClassPT,Xi:2003:GRD:604131.604150}. Usually
heterogeneous records contain values of kind |Type|. It makes sense since |Type|
is the kind of inhabited types, and records store values. Datatype constructors
take information with expressive kinds and wrap it on a uniform box. This is
desirable ins ome situations. In use cases such as our children records, where
we store a full featured attribution, we wish to state this on kinds. We
abstracted this notion and designed a library of polymporphic extensible
records, defined as follows:


> data Rec (c :: k) (r :: [(k', k'')]) :: Type where
>   EmptyRec  ::  Rec c '[]
>   ConsRec   ::  LabelSet ( '(l,v) ': r)
>             =>  TagField c l v -> Rec c r
>             ->  Rec c ( '(l, v) ': r)


A record is indexed by a parameter |c|, pointing out wich instance of record
we are defining, and a promoted list of pairs |r|. The kind of the first
component in each pair is polymorphic, since it is not mandatory that the type of
labels is inhabited; they need to live only at type level.
The second component is also polymorphic and it can have an elaborate kind.
|LabelSet| is a predicate that encodes the fact that there are no repeated
labels. 
|Tagfield| solves
the problem of wrapping and unwrapping some value so that each field actually stores
something with kind |Type|, keeping explicitly the information at type level.
%|TagField| is a fancier implementation of the well known |Data.Tagged| datatype:

> data TagField (c :: k) (l :: k') (v :: k'') where
>   TagField  ::  Label c -> Label l -> WrapField c v
>             ->  TagField c l v
%
where labels are proxies

> data Label (l :: k) = Label

The |TagField| constructor uses |Label| arguments to build instances because we
usually have them avaiable at term level, as we saw in the example of Section~\ref{sec:example},
but type applications\cite{conf/esop/EisenbergWA16} -or a much less elegant annotation- would work
fine. The third argument -of type |WrapField c v|- should be the value that we
want to tag. Note that |v| is kind polymorphic. For instance, a concrete instance
of |v| can be something like |[(Att, Type)]| in the case of children. When
actually creating a field to append in a record, an actual value must be stored;
this information must be Wrapped by a type constructor.
The type family
%
> type family WrapField (c :: k) (v :: k') :: Type
%
computes, depending on the index |c|, the wrapping of |v| under a suitable type
constructor. Note that if |v| is already inhabitated then |WrapField c| can be
the identity (type) function.

%We use some sugar to encode some of our functions as operators, for example,
%instead of |ConsRec| we usually use an infix operator |..*..|.

A relevant design decision is the implementation of the |LabelSet| constraint.
A similar type class is introduced on the {\tt HList} library,
where the property of non duplication of labels is implemented by the (recursive) instances of the class.
By using a type class to
encode a predicate, new instances can be defined anytime since type classes are open.
When an instance is not found, one could argue that this does not mean that the
predicate is |False|, but that the typechecker did not find a proof.
In the case of |LabelSet|, given a set of labels (if we know how to compare them)
the property is closed and decidable.
Also, to use our unified way to process type
errors we need to manipulate the truth value of the result.
For both arguments a
Boolean type family seems the way to go.
%
> type family LabelSetF (r :: [(k, k')]) :: Bool where
>   LabelSetF '[]          = True
>   LabelSetF [(l, v)]     = True
>   LabelSetF ( '(l, v) ': '(l', v') ': r)
>    = And3  (Not (l == l')) 
>            (LabelSetF ( '(l, v)   ': r) )
>            (LabelSetF ( '(l', v') ': r) )
%
where |(==)| is the type level equality operator (|Data.Type.Equality|).
Then we can encode the predicate as the following constraint.

> type LabelSet r = LabelSetF r ~ True

\subsection{Record Instances}

Most functions over records are implemented over the polykinded implementation
as part of the record library. Then we implement our actual record-like data
structures as particular instances of the general datatype. To introduce a
record we must give an index acting as a name (the ``|c|'' parameter),
and code the family instance |WrapField|.
To print the domain specific error messages
we can also need instances for |ShowField| and |ShowRec|, as we shall see
later.

Also, to code strongly kinded it is useful to specific datatypes for labels.

> data  Att    = Att Symbol Type
> data  Prod   = Prd Symbol NT
> data  Child  = Chi Symbol Prod (Either NT T)
> data  NT     = NT Symbol
> data  T      = T Type

|Att| is used for attributions, |Prod| for productions, and |Child|
for children.
In the following subsections we give some examples of record instances.

\subsubsection{Example: Attribution}

Attributions are mappings from attribute names to values. To make an index we
define an empty datatype:

> data AttReco

On the definition of |GenRecord| the |c| parameter is polykinded. We use the
kind |Type| for indexes in our instances since |Type| is an extensible kind.
Fixing the kind of this index the generic record library could allow a closed
set of records.

Attributions are records using the |AttReco| index. We define a descriptive name
and fix the polymorphic kinds since Attribution labels are of kind |Att|, and
fields of kind |Type|.

> type Attribution (attr :: [(Att, Type)]) = Rec AttReco attr
%
We do not need to actually wrap the fields since they are simply values:
%
> type instance  WrapField AttReco  (v :: Type) = v
%
We also use an specific name for fields:

> type Attribute (l :: Att) (v :: Type) = TagField AttReco l v

%if False
Pattern matching is a very useful feature in functional programming languages,
but somewhat incompatible with abstract datatypes.
Hiding constructors of |GenRecord| is nice but we lose pattern matching.
Fortunately, GHC Haskell implements pattern synonyms.
%endif
For each instance of record we can define specialized versions of the constructors
|TagField|, |EmptyRec| an |ConsAtt|, using the GHC Haskell's pattern synonyms\cite{pattern-synonyms}.
In the case of attributions this can be coded as follows:

> pattern  Attribute     ::  v -> TagField AttReco l v
> pattern  Attribute v   =   TagField Label Label v
> pattern  EmptyAtt      ::  Attribution '[]
> pattern  EmptyAtt      =   EmptyRec
> pattern  ConsAtt       ::  LabelSet ( '(att, val) ': atts)
>                        =>  Attribute att val -> Attribution atts
>                        ->  Attribution ( '(att,val) ': atts)
> pattern  ConsAtt a as  =   ConsRec att atts


\subsubsection{Example: Children Records}
Once again, we build an index:

> data ChiReco (prd :: Prod)

A child is associated to a production. Our instance has itself an index with
that information. Recall that |Prod| has a name for the production but also a
name for the non-terminal that it rewrites, so all this information is contained
on a child and used to check well formedness where it is used.
In this case the labels are of kind |Child|, and the values have a kind that
represents the list of associations attribute-value; i.e. an attribution.

> type ChAttsRec prd (chs :: [(Child,[(Att,Type)])])
>    = Rec (ChiReco prd) chs
%
|WrapField| takes the type information of the field, which is
not inhabited, and puts the |Attribution| wrapper.

> type instance  WrapField (ChiReco prd)  (v :: [(Att, Type)])
>   = Attribution v

%Again pattern synonyms are defined.


\subsection{Requirements}
\label{sec:requirements}
As a framework to encode type errors we introduce the concept of
requirements.

> class Require  (op   :: Type) (ctx  :: [ErrorMessage])  where
>    type ReqR op :: Type
>    req :: Proxy ctx -> op -> ReqR op


Given an operation |op|, that takes all the arguments needed for the current
operation to be performed, |req| extracts the tangible results, whose return
type depends on the operation. For example, each time we lookup in a record we
require that some label actually belongs to the record. If this requirement is
not accomplished an error must be raised at compile time.
The function |req| also uses some context information (i.e. the |trace| of the error)
to provide more useful information in the error message.

We collect the constraints imposed to a |Require| instance
in |RequireR|:
> type RequireR (op :: Type ) (ctx:: [ErrorMessage]) (res :: Type)
>     = (Require op ctx, ReqR op ~ res)

Some requirements such
as label equality are only about types, wich means that |req| is not used. It is
still useful to keep type errors in this framework, and in that case we use only
the |Require| constraint.

\begin{table}[t] 
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
   \caption{Example Requirements}\label{tab:req}
\end{table}

To pretty print type errors, we define a special operation:

> data OpError (m :: ErrorMessage) where {}
%
|OpError| is a phantom type containing some useful information to print.
A call to |OpError| happens when some requirement is not
fullfilled. Some examples of requirements implemented in our library are shown
on Table~\ref{tab:req}: A non satisfied requirement means that there will be no
regular instance of this class and it produces a |OpError| requirement.
When we call |req| with this operator the type checker reports an error since there is
only one instance:

> instance (TypeError (Text "Error: " :<>: m :$$:
>                      Text "trace: " :<>: ShowCTX ctx))
>   => Require (OpError m) ctx where {}
%
The type family |GHC.TypeLits.TypeError| works like the value-level function
|error|. When it is ``called'' a type error is raised, with a given error message
including a description |m| of the error and the context |ctx| where it occurred.
|TypeError| is so polymorphic that it can be used as a |Constraint|.
This generic instance is used to print all sort of type errors in a unified way,
otherwise catching type errors case by case would be difficult and error prone.
Note that specific information
of what happened is on |OpError| which is built from a specific instance of
|Require|, from a given operator and where every type relevant to show the error
message was in scope.

\subsubsection{Record Requirements: Lookup}
As an example of record requirements, we define the lookup operation.

> data OpLookup  (c  :: Type) (l  :: k) (r  :: [(k, k')]) :: Type where
>   OpLookup  ::  Label l -> Rec c r ->  OpLookup c l r
%
The operation is specified by an algebraic datatype, parametric on:
the record class, the index we are looking for, and the proper record.
The head label is inspected and depending on the
types the head value is returned or a recursive call is performed. To make
decisions over types, and set return types depending on arguments, we implement a
-sort of- dependent type function, which is encoded in Haskell with the usual
idioms of type-level programming. For instance, the proof of equality must be
made explicit using a proxy to help GHC to carry this type-level information. We
introduce a new |OpLookup'| with an auxiliary |Bool|ean at type-level:

> data OpLookup'  (b  :: Bool)
>                 (c  :: Type)
>                 (l  :: k)
>                 (r  :: [(k, k')]) :: Type where
>   OpLookup'  ::  Proxy b -> Label l -> Rec c r
>              ->  OpLookup' b c l r

For |OpLookup| we take the head label |l'| -there must be a head, otherwise we
are on the error instance that we introduce later- and use the auxiliary function
with the value equal to the predicate of equality of |l'| and the argument label
|l|:

> instance (Require (OpLookup' (l == l') c l ( '(l', v) ': r)) ctx)
>   =>  Require (OpLookup c l ( '(l', v) ': r)) ctx                  where
>   type ReqR (OpLookup c l ( '(l', v) ': r))
>     = ReqR (OpLookup' (l == l') c l ( '(l', v) ': r))
>   req ctx (OpLookup l r)
>     = req ctx (OpLookup' (Proxy @ (l == l')) l r)

%Implementing instances for |OpLookup'| is easy.
The instance of |OpLookup'| when |b==True|
corresponds to a |head| function, since we know that the searched label is on
the first position:

> instance Require (OpLookup' 'True c l ( '(l, v) ': r)) ctx where
>   type ReqR (OpLookup' 'True c l ( '(l, v) ': r))
>     = WrapField c v
>   req Proxy (OpLookup' Proxy Label (ConsRec f _))
>     = untagField f
%
Note that we set the return type to be |WrapField c v|, which is
completely generic.

When |b==True| a call to |OpLookup| on the tail of the record is performed:

> instance (Require (OpLookup c l r) ctx)
>   => Require (OpLookup' False c l ( '(l', v) ': r)) ctx where
>   type ReqR (OpLookup' False c l ( '(l', v) ': r))
>     = ReqR (OpLookup c l r)
>   req ctx (OpLookup' Proxy l (ConsRec _ r))
>     = req ctx (OpLookup l r)


When we try to lookup into an empty record an error happened:
We went over all the record
and there was no value tagged with the searched label.
Here we build a pithy instance of |OpError|:

> instance Require (OpError
>     (     Text "field not Found on "  :<>: Text (ShowRec c)
>     :$$:  Text "looking up the "      :<>: Text (ShowField c)
>     :<>:  ShowT l )) ctx
>   => Require  (OpLookup c l ( '[]  :: [(k, k')])) ctx where
>   type ReqR   (OpLookup c l ('[]   :: [(k, k')])  ) = ()
>   req = undefined


This procedure is recurrent in all our development:
\begin{itemize}
\item Code dependent Haskell, if everything goes well neither
  we access bad indexes nor rules at incorrect productions were used, etc.
\item Encode the bad cases, requiring an |OpError|. Note that when building it,
  like in the former |Require| instance for |OpLookup| a lot of information
  about types is on scope and can be used to make up an informative error.
\end{itemize}

Then, when the user tries to access a bad index, at compile time the type
checker triggers a type error when type class resolution comes upon this
singleton instance of |OpError|.

In the former definition |ShowRec| and |ShowField| type families were used to
pretty print the type information depending on which instance of records we
are working on.

> type family ShowRec    (c :: k)    :: Symbol
> type family ShowField  (c :: k)    :: Symbol

For instance, for attributions we implement:

> type instance ShowRec    AttReco  = "Attribution"
> type instance ShowField  AttReco  = "attribute named "

For children:

> type instance ShowRec    (ChiReco a) = "Children Map"
> type instance ShowField  (ChiReco a) = "child labelled "

The fact that type families can be open is very convenient in this
context, new records can be defined in a customized and modular way.
We think that |Require| and |GenRecord| transcend the status of internal modules for
\AspectAG\ and are useful as a standalone library on their own.

The |ShowT| family is also interesting:

> type family ShowT (t :: k) :: ErrorMessage

When we print labels which are types with kinds such as |Att|, |Prd| or |Chi|,
to show clear type errors we should print them in a different way
depending on the case, formatting the information correctly. At term level a
fully polymorphic function cannot touch its arguments. Type classes are the way
to define bounded parametricity. Haskell does not provide kind classes but they
are not necessary since polykinded type families are actually not parametric.
When programming at type level we can actually inspect kinds and pattern match
on them as using {\bf |typeOf|} in languages where types are avaiable at run
time. Therefore, the following definitions are completely legal:

> type instance  ShowT ('Att l t)
>   =     Text  "Attribute "  :<>: Text l
>   :<>:  Text  ":"           :<>: ShowT t
> type instance  ShowT ('Prd l nt)
>   =     ShowT nt :<>: Text "::Production "
>   :<>:  Text l
%
and so on. Also, we can build an instance for any type of kind |Type|, so
inhabited types are printed with their standard name:

> type instance ShowT (t :: Type)
>   = ShowType t



\subsubsection{Label Equality Requirements}

We use |RequireEq| to require label (and thus type) equality,
wich is actually a sugar for a couple of constraints:

> type RequireEq (t1 :: k )(t2 :: k) (ctx:: [ErrorMessage])
>     = (Require (OpEq t1 t2) ctx, t1 ~ t2)

The first is a requirement, using the following operator:

> data OpEq t1 t2
> instance RequireEqRes t1 t2 ctx
>   => Require (OpEq t1 t2) ctx where
>   type ReqR (OpEq t1 t2) = ()
>   req = undefined

Notice that in this case we do not define an implementation for the function
|req|, since this requirement is used only at type-level.
The type family |RequireEqRes| is a type-level function computing a constraint.
It reduces to the requirement of an |OpError| if $t1 \neq t2$, building a
readable error message, or to the trivial (Top) constraint otherwise.


> type family  RequireEqRes (t1 :: k) (t2 :: k)
>              (ctx :: [ErrorMessage]) ::  Constraint where
>   RequireEqRes t1 t2 ctx
>           = If   (t1 `Equal` t2)
>                  (() :: Constraint)
>                  (Require (OpError  (Text "" :<>: ShowT t1
>                                     :<>: Text " /= " :<>: ShowT t2)) ctx)

