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
In order to provide flexibility, safety, and achieve error messages as the ones
shown in the previous section, \AspectAG\ internals are built from strongly typed
extensible records.
Mistakes due to references to lacking fields (Section~\ref{sec:errref})
%%like trying to access to an undefined attribute or child
are detected at compile time as an incorrect look up in a given record.
Also, the definition of duplicated attributes (Section~\ref{sec:errdup}) results in a type error, due to an
incorrect record extension.
%% However, detecting errors is not enough. If the error messages are difficult to
%% understand and do not give references to their possible points of introduction
%% within the source code, then using the library becomes a painful task. A common
%% problem of type-level programming implementations of EDSLs is the leakage of
%% implementation details in error messages. This was the case of the previous
%% version of \AspectAG.
%It is a common problem when implementing EDSLs using type-level programming that when a type
% error occurs, implementation details are leaked on error messages,
% and this was the case of the previous version of \AspectAG.
Then using user-defined type errors, a tool introduced in GHC to
help improving the quality of type-level programming error messages, custom
error messages are printed out using the type family |GHC.TypeLits.TypeError|.
%However, using this tool it is not clear how to structure the implementation in a
%modular, dependable and scalable way.

In this section we show an implementation of extensible records and introduce a
framework to encode EDSL type errors that keeps track of the possible sources of
errors.

%On section \ref{sec:requirements} we present our solution.

\subsection{Polymorphic Heterogeneous Records}

%We use multiple instances of extensible records:
The implementation of the library is strongly based on the use of extensible records. They are used in the representation of:

\begin{itemize}
\item
  |Attribution|s, which are mappings from attribute names to values. In our example, |eval| and |env|, defined in Figure~\ref{fig:eval}, are labels of such records.
\item
  For each production, there is a set of children, each one with an associated
  attribution.
  % Note that
  In this case each field is not a flat value, but a full
  record by itself. The labels in the example are: |leftAdd|, |rightAdd|, |ival| and |vname|.
  % It would be nice to reflect it on types.
\item
  \emph{Aspects}, which are records of rules indexed by productions. In this case the labels are: |add|, |val| and |var|.
\item
  Semantic functions, which are kept in a record (not visible by the user).
\end{itemize}

Extensible records coded using type-level programming are already well known in
the Haskell community. The {\tt HList}
library~\cite{Kiselyov:2004:STH:1017472.1017488} popularized them. One common
way to implement a record is by using a GADT indexed by the list of types of the
values stored in its fields. These types are usually of kind |Type|, what makes
sense since |Type| is the kind of inhabited types, and records store values.
However, in cases such as our children records, where we store attributions that
are also represented by an indexed GADT, we would like to be able to reflect
some of this structural information at the indexes of the record. This can be
achieved if we are polymorphic in the kind of the types corresponding to the
record fields. Based on this approach we designed a new, polykinded, extensible
record structure:

%We abstracted this notion and designed a library of polymporphic extensible
%records, defined as follows:


> data Rec (c :: k) (r :: [(k', k'')]) :: Type where
>   EmptyRec  ::  Rec c '[]
>   ConsRec   ::  LabelSet ( '(l,v) ': r)
>             =>  TagField c l v -> Rec c r ->  Rec c ( '(l, v) ': r)


A record is indexed by a parameter |c|, pointing out which instance of record
we are defining (e.g. attribution, set of children, aspect, etc.),
and a promoted list of pairs |r| representing the fields.
The first component of each pair is the label.
The kind |k'| is polymorphic, since it is not mandatory to the type of
labels to be inhabited; they need to live only at type level.
The second component is also polymorphic and it can have an elaborate kind |k''|.
By doing this, in the cases where the type of a stored value is an indexed GADT, we
can use its index as the index that represents the field.
|Tagfield| is the type of the fields of our records.
%solves
%the problem of wrapping and unwrapping some value so that each field actually stores
%something with kind |Type|, keeping explicitly the information at type level.

> data TagField (c :: k) (l :: k') (v :: k'') where
>   TagField  ::  Label c -> Label l -> WrapField c v
>             ->  TagField c l v
>
> data Label (l :: k) = Label

Labels are proxies, notice that all the labels in Section~\ref{sec:example} are defined using the constructor |Label|,
varying the phantom type.
%The |TagField| constructor uses |Label| arguments to build instances because we
%usually have them avaiable at term level, as we saw in the example of Section~\ref{sec:example},
%but type applications\cite{conf/esop/EisenbergWA16} -or a much less elegant annotation- would work
%fine.
The third argument -of type |WrapField c v|- should be the value that we
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

|LabelSet| is a predicate that encodes the fact that there are no repeated
labels. 
A relevant design decision is the implementation of the |LabelSet| constraint.
A type class with similar semantics is introduced on the {\tt HList} library,
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
>   LabelSetF '[]                    = True
>   LabelSetF ( '(l, v)  ': '[])     = True
>   LabelSetF ( '(l, v)  ': '(l', v') ': r)
>    = And3  (Not (l == l')) 
>            (LabelSetF ( '(l, v)   ': r) )
>            (LabelSetF ( '(l', v') ': r) )
%
where |(==)| is the type level equality operator (|Data.Type.Equality|), and
|And3| a type family computing the conjunction of three boolean arguments. Then we
can encode the predicate as the constraint:

> type LabelSet r = LabelSetF r ~ True

\subsection{Record Instances}

In our library most functions over records are implemented over the generic
  implementation. After that we implement our record-like data structures as
  particular instances of the general datatype. To introduce a new record
  structure we must give an index acting as a name (the ``|c|'' parameter), and
  code the family instance |WrapField|. As we shall see later, in order to print
  out domain specific error messages we also need to provide instances for the
  type families |ShowField| and |ShowRec|.

To code in a strongly kinded way, it is also useful to provide specific datatypes for labels,
where |Att| is used for attributions, |Prod| for productions, and |Child| for children.


> data  Att    = Att Symbol Type
> data  Prod   = Prd Symbol NT
> data  Child  = Chi Symbol Prod (Either NT T)
> data  NT     = NT Symbol
> data  T      = T Type


We give some examples of record instances, that we use in our implementation of \AspectAG.

\subsubsection*{Example: Attribution}

Attributions are mappings from attribute names to values.
%To make an index we define an empty datatype:
We instance |Rec| with an empty datatype |AttReco| as index. We define a descriptive name
and fix the polymorphic kinds, since Attribution labels are of kind |Att|, and
fields of kind |Type|.

> data AttReco
>
> type Attribution (attr :: [(Att, Type)]) = Rec AttReco attr
%
The label |add|, with type |Label ('Prd "Add" Nt_Expr)|, 
of Section~\ref{sec:example} is an example of a valid |Attribution| label.

\noindent We do not need to wrap the fields since they are simply values:
%
> type instance  WrapField AttReco  (v :: Type) = v
%
We also use an specific name for fields:

> type Attribute (l :: Att) (v :: Type) = TagField AttReco l v

%if False
Pattern matching is a very useful feature in functional programming languages,
but somewhat incompatible with abstract datatypes.
Hiding constructors of |Rec| is nice but we lose pattern matching.
Fortunately, GHC Haskell implements pattern synonyms.
%endif
%For each record instance
We can define specialized versions of the constructors
|TagField|, |EmptyRec| and |ConsAtt| by using GHC's pattern synonyms~\cite{pattern-synonyms}.
%In the case of attributions this can be coded as follows:

> pattern  Attribute     ::  v -> TagField AttReco l v
> pattern  Attribute v   =   TagField Label Label v
> pattern  EmptyAtt      ::  Attribution '[]
> pattern  EmptyAtt      =   EmptyRec
> pattern  ConsAtt       ::  LabelSet ( '(att, val) ': atts)
>                        =>  Attribute att val -> Attribution atts
>                        ->  Attribution ( '(att,val) ': atts)
> pattern  ConsAtt a as  =   ConsRec att atts


\subsubsection*{Example: Children Records}
%Once again, we build an index:

A child is associated to a production. Our instance has itself an index with
this information. Recall that |Prod| has a name for the production but also a
name for the non-terminal that it rewrites, so all this information is contained
on a child and used to check well formedness where it is used.
In this case the labels are of kind |Child|, and the values have a kind that
represents the list of associations attribute-value; i.e. an attribution.

> data ChiReco (prd :: Prod)
>
> type ChAttsRec prd (chs :: [(Child,[(Att,Type)])])
>    = Rec (ChiReco prd) chs
%
|WrapField| takes the type information of the field, which is
not inhabited, and puts the |Attribution| wrapper.

> type instance  WrapField (ChiReco prd)  (v :: [(Att, Type)])
>   = Attribution v

%Again pattern synonyms are defined.
Examples of types of Attribution labels of the example are:
< rightAdd  :: Label ('Chi "rightAdd"  P_Add  ('Left Nt_Expr))
< ival      :: Label ('Chi "ival"   P_Val  ('Right ('T Int)))

\subsection{Requirements}
\label{sec:requirements}
As a framework to encode type errors we introduce the concept of
requirements.

> class Require  (op   :: Type) (ctx  :: [ErrorMessage])  where
>    type ReqR op :: Type
>    req :: Proxy ctx -> op -> ReqR op

Some functions require that specific non trivial conditions are met on types, or
a type error must occur otherwise. For instance, each time we look up in a record we require
that some label actually belongs to the record. Given an operation represented by a datatype |op|,
that takes all the arguments needed for the current operation to be
performed, |req| extracts the tangible results, whose return type depends on the
operation. The function |req| also uses some context information |ctx|  (i.e. the
|trace| of the error) to provide more useful information in the error message.

We collect the constraints imposed to a |Require| instance
in |RequireR|:
> type RequireR (op :: Type ) (ctx:: [ErrorMessage]) (res :: Type)
>     = (Require op ctx, ReqR op ~ res)

Some requirements such
as label equality are only about types, which means that |req| is not used. It is
still useful to keep type errors in this framework, and in that case we use only
the |Require| constraint.

%% \begin{table}[t] 
%%    \small % text size of table content
%%    \centering % center the table
%%    \begin{tabular}{lcr} % alignment of each column data
%%    \toprule[\heavyrulewidth] \textbf{Operation} & \textbf{Requirement} &
%%    \textbf{Require Operator} \\ \midrule Record Lookup & label is a member &
%%    |OpLookup| \\ \hline Record Update & label is a member & |OpUpdate| \\ \hline
%%    Record Extension & label is not a member & |OpExtend| \\ \hline New
%%    synthesized attribute & {\begin{minipage}[t]{.3\linewidth}\begin{center}
%%          attribute type $\equiv$ \\type of definition \end{center}\end{minipage}}
%%    & |RequireEq| \\ \hline New inherited attribute &
%%    {\begin{minipage}[t]{.3\linewidth}\begin{center} attribute type $\equiv$ \\type
%%          of definition \end{center}\end{minipage}}& |RequireEq| \\ \hline
%%    New inherited
%%    attribute & {\begin{minipage}[t]{.3\linewidth}\begin{center}
%%          argument production \\$\equiv$ child production
%%    \end{center}\end{minipage}}& |RequireEq|
%%    \\ \bottomrule[\heavyrulewidth]
%%    \end{tabular}
%%    \caption{Example Requirements}\label{tab:req}
%% \end{table}

To pretty print type errors, we define a special operation:

> data OpError (m :: ErrorMessage)
%
|OpError| is a phantom type containing some useful information to print.
A call to |OpError| happens when some requirement is not
fulfilled.
%%Some examples of requirements implemented in our library are shown on Table~\ref{tab:req}:
A non satisfied requirement means that there will be no
regular instance of this class and it produces a |OpError| requirement.
When we call |req| with this operator the type checker reports an error since
the instance is:

> instance (TypeError (  Text "Error: " :<>: m :$$:
>                        Text "trace: " :<>: ShowCTX ctx))
>   => Require (OpError m) ctx
%
The type family |GHC.TypeLits.TypeError| works like the value-level function
|error|. When it is evaluated at compile time a type error is raised,
with a given error
message including a description |m| of the error and the context |ctx| where it
occurred. |TypeError| is completely polymorphic so it can be used with kind
|ErrorMessage -> Constraint| as we do here.
This generic instance is used to print all sort of type errors in
a unified way, otherwise catching type errors case by case would be difficult
and error prone. Note that specific information of what happened is on |OpError|
which is built from a specific instance of |Require|, from a given operator and
where every type relevant to show the error message was in scope.

\subsubsection{Record Requirements: Lookup}\label{sec:lookup}
As an example of record requirements, we define the lookup operation.

> data OpLookup  (c  :: Type) (l  :: k) (r  :: [(k, k')]) :: Type where
>   OpLookup  ::  Label l -> Rec c r ->  OpLookup c l r
%
The operation is specified by an algebraic datatype, parametric on:
the record class (|c|), the index we are looking for (|l|),
and the proper record (|r|).
The head label is inspected and depending on the
types the head value is returned or a recursive call is performed. To make
decisions over types, and set return types depending on arguments, we implement a
dependent type function, which is encoded in Haskell with the usual
idioms of type level programming. For instance, the proof of equality must be
made explicit using a proxy to help GHC to carry this type level information. We
introduce a new |OpLookup'| with an auxiliary |Bool|ean at type level:

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

When |b==False| a call to |OpLookup| on the tail of the record is performed:

> instance (Require (OpLookup c l r) ctx)
>   => Require (OpLookup' False c l ( '(l', v) ': r)) ctx where
>   type ReqR (OpLookup' False c l ( '(l', v) ': r))
>     = ReqR (OpLookup c l r)
>   req ctx (OpLookup' Proxy l (ConsRec _ r))
>     = req ctx (OpLookup l r)


When we try to look up in an empty record an error happens:
we went over all the record
and there was no value tagged with the searched label.
Here we require the instance of |OpError| informing the actual error:

> instance Require (OpError
>     (     Text "field not Found on "  :<>: Text (ShowRec c)
>     :$$:  Text "looking up the "      :<>: Text (ShowField c)
>     :<>:  ShowT l )) ctx
>   => Require  (OpLookup c l ( '[]  :: [(k, k')])) ctx where
>   type ReqR   (OpLookup c l ('[]   :: [(k, k')])  ) = ()
>   req = undefined


Notice that this error message is the one we obtain in Section~\ref{sec:errref},
when trying to access to an undefined attribute |foo|.

This procedure is recurrent in all our development:
\begin{itemize}
\item Use requirements for operations that can introduce DSL errors,
      keeping track of the call trace in the |ctx| index.
\item Encode the bad cases, requiring an |OpError|.
%  Note that when building it,
%  like in the former |Require| instance for |OpLookup| a lot of information
%  about types is on scope and can be used to make up an informative error.
\end{itemize}

Then, when the user does not fulfill a requirement, the type
checker triggers a type error since type class resolution comes upon this
singleton instance of |OpError|.

In the previous definition |ShowRec| and |ShowField| type families were used to
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
context; new records can be defined in a customized and modular way.
We think that |Require| and |Rec| transcend the status of internal modules for
\AspectAG\ and are useful as a standalone library on their own.

The |ShowT| family is also interesting:

> type family ShowT (t :: k) :: ErrorMessage

When we print labels (with kinds such as |Att|, |Prd| or |Chi|)
to show clear type errors we should print different information
depending on the kind.
%At term level a
%fully polymorphic function cannot touch its arguments. Type classes are the way
%to define bounded parametricity.
This imposes some sort of ad-hoc polymorphism at the kind level.
Haskell does not provide such \emph{kind classes}, but they
are not necessary since polykinded type families are actually not parametric.
When programming at type level we can actually inspect kinds and pattern match
on them as using {\bf |typeOf|} in languages where types are avaiable at run
time. Therefore, the following definitions are completely legal:

> type instance  ShowT ('Att l t)
>   =  Text "Attribute " :<>: Text l :<>: Text  ":" :<>: ShowT t
> type instance  ShowT ('Prd l nt)
>   =  ShowT nt :<>: Text "::Production " :<>:  Text l
%
and so on. Also, we can build an instance for any type of kind |Type|, so
inhabited types are printed with their standard name:

> type instance ShowT (t :: Type)  = ShowType t

Then, for example in Section~\ref{sec:errref} the error messages say ``{\small\texttt{Attribute eval:Int}}'' when
referring to the attribute |eval| and ``{\small\texttt{Non-Terminal Expr::Production Add}}'' when referring to the
production |add|.

\subsubsection{Label Equality Requirements}

We use |RequireEq| to require label (and thus type) equality,
which is actually a sugar for a couple of constraints:

> type RequireEq (t1 :: k )(t2 :: k) (ctx:: [ErrorMessage])
>     = (Require (OpEq t1 t2) ctx, t1 ~ t2)

The first constraint is a requirement, using the following operator:

> data OpEq t1 t2
> instance RequireEqRes t1 t2 ctx
>   => Require (OpEq t1 t2) ctx where
>   type ReqR (OpEq t1 t2) = ()
>   req = undefined

Notice that in this case we do not define an implementation for the function
|req|, since this requirement is used only at type level.
The type family |RequireEqRes| is a type level function computing a constraint.
It reduces to the requirement of an |OpError| if $t1 \neq t2$, building a
readable error message, or to the trivial (Top) constraint otherwise.


> type family  RequireEqRes (t1 :: k) (t2 :: k)
>              (ctx :: [ErrorMessage]) ::  Constraint where
>   RequireEqRes t1 t2 ctx
>           = If   (t1 `Equal` t2)
>                  (() :: Constraint)
>                  (Require (OpError  (Text "" :<>: ShowT t1
>                                     :<>: Text " /= " :<>: ShowT t2)) ctx)

This is the kind of error message that appears in \ref{sec:errexp} and in most of the examples of \ref{sec:errref},
where the actual type is not the expected.
