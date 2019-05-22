%if False

> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE
>              TypeFamilies,
>              FlexibleContexts,
>              ScopedTypeVariables,
>              NoMonomorphismRestriction,
>              ImplicitParams,
>              ExtendedDefaultRules,
>              UnicodeSyntax,
>              DataKinds,
>              TypeApplications,
>              PartialTypeSignatures,
>              AllowAmbiguousTypes
> #-}

> module ExprPaper where

> import System.Exit (exitFailure)
> import Language.Grammars.AspectAG
> import Control.Monad
> import Control.Applicative
> import Data.Proxy
> import GHC.TypeLits
> import Data.Map
> import Data.Maybe
> import Debug.Trace


%endif

Higher order functions such as |foldr| are powerful abstraction tools for the
functional programmer. Given a data type we capture the structural recursion
scheme by giving a function for each constructor to combine contained data and
recursive calls. From the algebraic perspective the programmer must provide an
\emph{algebra} capturing semantics for the grammar -or data type, note that
there is a clear correspondence between both formalisms-, and the
\emph{catamorphism} builds the computation. However in practice, when
constructing real world compilers, many problems arise. Abstract syntax trees
tend to have a lot of alternatives (meaning huge algebras). Some information
must flow top down, and actually many orthogonal (or not) alternative semantics
are needed (well formedness properties, free variables, type checking,
evaluation..). Also, it is common that abstract syntax trees evolve with time,
when new constructs are added to the language, breaking every algebra.

More in general, given a functional program it is easy to extended it by
defining new functions. However, extending data (for example, if a datatype is
extended with a new constructor) is not easy. Each case expression where a value
of this type is matched has to be inspected and modified accordingly. On the
other side, object oriented programing is good to define new data: one could
implement algebraic datatypes with a composite design pattern, and simply add a
new class. However, to define a new function for a data type, we have to inspect
all the existing subclasses and add a new method. This problem was first noted
by Reynolds [REF] and later referred to as “the expression problem” by Wadler
\cite{ExpressionProblem}. Attribute grammars offer an aproach to solve this
issue.

Attribute grammars were originally introduced to describe semantics for context
free languages\cite{Knuth68semanticsof}. Given a grammar, we associate
attributes to each production. Attribute values are computed from semantic rules
given by the implementator in every node of the abstract syntax tree in terms of
the attribute values of the children and the parent. Usually attributes are
classified in at least two sets: synthesized attributes (where information flows
bottom up) and inherited attibutes (where it flows top down).

%format expr_l = "expr_l"
%format expr_r = "expr_r"

\section{Overview of the library}

As a running example consider a simple expression language given by the following grammar,
including integer values (|ival|), variables (|vname|) and addition:

<  expr    ->  ival
<  expr    ->  vname
<  expr    ->  expr_l + expr_r


To keep it simple, we cannot bind variables with this constructs for now.
Let us assume that they actually denote some value clear from a given context.
For example, a concrete expression $x + 5 + 2$, if we know from the context that $x = 2$, evaluates to $9$.

Note that we have introduced one non-terminal, called |expr|,
with three productions. |ival| and
|vname| are names for terminals, with types |Integer| and |String|,
respectively. We say they are \emph{children} in their productions.

The third production rewrites a non-terminal into two
non-terminals. Each child must have a name, to be able to refer to it.

In our embedded DSL this grammar is declared as follows:

Declare one non-terminal:

> type Nt_Expr = 'NT "Expr"
> expr = Label @ Nt_Expr

with three productions:

> type P_Add = 'Prd "p_Add" Nt_Expr
> add = Label @ P_Add

> type P_Val = 'Prd "p_Val" Nt_Expr
> val = Label @ P_Val

> type P_Var = 'Prd "p_Var" Nt_Expr
> var = Label @ P_Var

and four different children:

> leftAdd   = Label @ ('Chi "leftAdd"   P_Add
>                                       ('Left Nt_Expr))
> rightAdd  = Label @ ('Chi "rightAdd"  P_Add
>                                       ('Left Nt_Expr))
> ival      = Label @ ('Chi "ival"   P_Val
>                                    ('Right ('T Int)))
> vname     = Label @ ('Chi "vname"  P_Var
>                                    ('Right ('T String)))

%This is simpler than it seems.
Non-terminals are defined by names (like
|"Expr"|). Note that we are using a promoted |String| here, the kind |Symbol| in
modern Haskell. Productions are also identified by a name, and are related to a
non-terminal. Children are once more names, tied to a production and |Either| a
non-terminal or a terminal. Everything is wrapped on constructors of simple
algebraic data kinds, since we implement everything strongly typed both at term
level, and at type level. |Label| is actually a |Proxy| with an alternative name
adecuated to our domain. Everything is defined at type-level but we will use
this proxies as carriers of type information.
A widely used idiom in type-level programming.


The abstract syntax tree for this grammar can be implemented in Haskell,
for example, with the datatype:

> data Expr  =  Val  { ival'    :: Int  }
>            |  Var  { vname'   :: String   }
>            |  Add  { l', r'   :: Expr     }
%
%if False
>       deriving Show
%endif
%
where the previous example expression is represented with the value:

|Add (Add (Var "x") (Val 5)) (Val 3)|.

%if False
The user of our library could define the Haskell implementation of the abstract
syntax tree to extract from it a lot of boilerplate using Template
Haskell\cite{Sheard:2002:TMH:636517.636528} utilities that we provide.
But the
constructions that we provide are datatype independent, which is useful to
actually solve the expression problem, as we shall discuss later.
%endif
In our library we provide some Template Haskell\cite{Sheard:2002:TMH:636517.636528}
functions that can be used to generate the grammar definition
(non-terminals, productions and children)
out of a datatype representing the abstract syntax tree (e.g. |Expr|).
However, our grammar representation is independent of such datatypes,
which is actually useful to solve the expression problem, as we shall discuss later.


Attribute grammars decorate the productions of context-free grammars with
\emph{attribute} computations, in order to provide semantics to such grammars.
In our example the semantics consist on the evaluation of the expressions.
To define the semantics we can use two attributes: one to represent
the result of the evaluation %(that is certainly synthesized)
and one to distribute
the context defining semantics for variables.

> eval = Label @ ('Att "eval" Int)
> env  = Label @ ('Att "env"  (Map String Int))



% Time to define semantics.
The attribute |eval| denotes the value of an
expression. It is computed on the |add| production as the sum of the denotation
of subexpressions. On each subexpression there is a proper attribute |eval| that
contains its value. This is written on AspectAG as:

> add_eval  =  syndefM eval add
>           $ (+) <$> at leftAdd eval <*> at rightAdd eval

The function syndef takes an attribute (for wich the semantics are being
defined) and a production (where it is being defined). In this case function
|syndefM| defines a rule for the attribute |eval| at profuction |add|. The last
argument is the proper definition. We take the values of |eval| at children
|leftAdd| and |rightAdd|, and combine them with the operator |(+)|.

At |val| production, where the grammar rewrites to a terminal, the value of that
 terminal corresponds to the semantics of the expression. In terms of our
 implementation the attribute |eval| is defined at |val| as the value of the
 terminal |ival|.

> val_eval = syndefM eval val
>          $ ter ival

|ter| is simply a reserved keyword in our EDSL.

Finally on variables, the expression denotes the value of the variable on a
given context. This is implemented as follows:

> var_eval = syndefM eval var $ slookup
>           <$> ter vname <*> at lhs env
>    where slookup nm = fromJust . Data.Map.lookup nm

We look at the terminal |vname|, and look for the attribute |env|
on the inherited attributes. The collection of inherited attributes is
accesed by the name |lhs| on the same way that we have acces to the synthesized
attributes using the name of each children. We call this collections of attributes
\emph{attributions}.

Finally, we combine all this rules on an \emph{aspect}:


> aspEval   =  traceAspect (Proxy @ ('Text "eval"))
>           $  add_eval .+: val_eval .+: var_eval .+: emptyAspect

Before understand what is going on with this |traceAspect| wrapper, lets say
that the operator |(.+:)| is simply a combinator that adds a rule to an aspect
(it associates to the right). In our EDSL domain an aspect is a collection of
rules. Here we build an aspect with all the rules for a given attribute, but the
user can combine them in the way he or she wants (for example, by production).
Aspects can be orthogonal to one another, or not. Here |aspEval| clearly depends
on an attribute |env| with no rules attached to it at this point, so it is not
useful at all. We cannot complain here yet since the rules for |env| could we
defined later (as we will do), or perhaps in another module! If we try to
actually use |aspEval| calling it on a semantic function, there will be a type
error, but it will be raised on the semantic function application. The function
|traceAspect|, and also -implicitly- each application of |syndefM| tag
definitions to show them on type errors. This is useful to debug and we
encourage to use tags, but it is optional.

For the inherited attribute |env| we provide the |inhdefM| combinator, wich
takes an attribute name, a production where the rule is being defined, and a
child for what the information is being distributed. In our example |env| is
copied to both children on |add| production, so we build one rule for each:

> add_leftAdd_env  = inhdefM env add leftAdd  $ at lhs env
> add_rightAdd_env = inhdefM env add rightAdd $ at lhs env

and combine them on an aspect:

> aspEnv  =  traceAspect (Proxy @ ('Text "env"))
>         $  add_leftAdd_env .+: add_rightAdd_env .+: emptyAspect 

We can combine aspects with the |(.:+:)| operator:

> asp = aspEval .:+: aspEnv

Note that this time we decided to not make a new tag.

Finally, given an implementation of the abstract syntax tree, like |Tree| we can
encode (or derive) the \emph{semantic function}. |sem_Expr| takes an aspect, an
AST and an initial attribution and computes semantics for that expression.
The result is an attribution with all the synthesized attributes of the root. We
can define an evaluator:

> evalExpr e m = sem_Expr asp e (env =. m .*. emptyAtt) #. eval

that takes an environment |m| mapping variable names to |Int|s.
For example this definition

> exampleExpr =  Add (Add (Var "x") (Val 5)) (Val 2)
> exampleEval =  evalExpr exampleExpr (insert "x" 5 Data.Map.empty)

evaluates to |12| % \eval{exampleEval}




%if False

> sem_Expr asp (Add l r) = knitAspect add asp
>                            $  leftAdd  .=. sem_Expr asp l
>                           .*. rightAdd .=. sem_Expr asp r
>                           .*.  EmptyRec
> sem_Expr asp (Val i)   = knitAspect val asp$
>                           ival  .=. sem_Lit i .*. EmptyRec
> sem_Expr asp (Var v)   = knitAspect var asp$
>                           vname .=. sem_Lit v .*. EmptyRec

%endif

\subsection{Semantic Extension: Adding attributes}

Defining alternative semantics or extending the already defined ones is simple.
 For example, suppose that we want to collect the integral literals
occurring on an expression. Define an attribute |lits|:

> lits  = Label @ ('Att "lits"  [Int])

And the rules to compute it. This time we combine them on the fly:

> aspLits
>    =   syndefM lits add ((++) <$> at leftAdd lits <*> at rightAdd lits)
>   .+:  syndefM lits val ((\x -> [x]) <$> ter ival)
>   .+:  syndefM lits var (pure [])
>   .+:  emptyAspect

The function:

> litsExpr e = sem_Expr aspLits e emptyAtt #. lits

returns a list of all literals occurring in the expression, in order.

\subsection{Grammar extension: Adding Productions}

To tackle the expression problem we must be able to extend our grammar.

\begin{figure}
\caption{Grammar plus extension}
\centering

<  expr    ->  ival
<  expr    ->  vname
<  expr    ->  expr_l + expr_r

%\hline

< expr     -> let vname = expr_d in expr_i

\end{figure}


Suppose that we add a new production to add local definitions:

< expr     -> let vname = expr_d in expr_i

We implement them with this definition:

> type P_Let = 'Prd "p_Let" Nt_Expr
> elet = Label @ P_Let

This new production has three children

> exprLet   = Label @ ('Chi "exprLet"   P_Let ('Left Nt_Expr))
> bodyLet   = Label @ ('Chi "bodyLet"   P_Let ('Left Nt_Expr))
> vlet      = Label @ ('Chi "vlet"      P_Let ('Right ('T String)))




> aspEval2
>   =  traceAspect (Proxy @ ('Text "eval2"))
>   $  syndefM eval elet (at bodyLet eval) .+: aspEval


> aspEnv2
>   =    traceAspect (Proxy @ ('Text "env2"))
>   $    inhdefM env elet exprLet (at lhs env)
>   .+:  inhdefM env elet bodyLet (insert   <$>  ter vlet
>                                           <*>  at exprLet eval
>                                           <*>  at lhs env)
>   .+:  aspEnv


> asp2 = aspEval2 .:+: aspEnv2
