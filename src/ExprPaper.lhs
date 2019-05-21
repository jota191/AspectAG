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

> module Expr where

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
[REF]. Attribute grammars offer an aproach to solve this issue.

Attribute grammars were originally introduced to describe semantics for context
free languages[REF]. Given a grammar, we associate attributes to each
production. Attribute values are computed from semantic rules given by the
implementator in every node of the abstract syntax tree in terms of the
attribute values of the children and the parent. Usually attributes are
classified in at least two sets: synthesized attributes (where information flows
bottom up) and inherited attibutes (where it flows top down). 


\section{Overview of the library}

As a running example consider a simple expression language given by the
grammar:

<  expr    ->  ival
<  expr    ->  vname
<  expr    ->  expr_l + expr_r


To keep it simple, we cannot bind variables with this constructs for now.
Lets assume that they actually denote some value clear from a given context.
A concrete expression $(x + 5) + 2$  If we now from the context that $x = 2$
then the evaluation results in $10$.

The abstract syntax tree for this grammar could be implemented in Haskell as:

< data Expr  =  Val  { ival   :: Integer  }
<            |  Var  { vname  :: String   }
<            |  Add  { l, r   :: Expr     }

%if False

<        deriving Show

%endif


where the former example expression could be parsed to
|Add (Add (Var "x") (Val 5)) (Val 3)|.

The user of our library could define the Haskell implementation of the abstract
syntax tree to extract from it a lot of boliterplate using Template Haskell
[REF] utilities that we provide. But the constructions that we provide are data
type independant, which is useful to actually solve the expression problem, as
we shall discuss later.


Note that we have introduced three productions in this the example. |ival| and
|vname| are names for terminals, whose type are |Integer| and |String|
respectively. They are \emph{children} in their productions.

The third production rewrites a non-terminal into two
non-terminals. Each children must have a name, to refer to them.
There is only one non-terminal called |expr|.

In our embedded DSL this is declared as follows:

Declare one non terminal:

> type Nt_Expr = 'NT "Expr"
> expr = Label @ Nt_Expr

and three productions:

> type P_Add = 'Prd "p_Add" Nt_Expr
> add = Label @ P_Add

> type P_Val = 'Prd "p_Val" Nt_Expr
> val = Label @ P_Val

> type P_Var = 'Prd "p_Var" Nt_Expr
> var = Label @ P_Var

We declare also the four different children:

> leftAdd   = Label @ ('Chi "leftAdd"   P_Add ('Left Nt_Expr))
> rightAdd  = Label @ ('Chi "rightAdd"  P_Add ('Left Nt_Expr))
> ival      = Label @ ('Chi "ival"      P_Val ('Right ('T Int)))
> vname     = Label @ ('Chi "vname"     P_Var ('Right ('T String)))

This is simpler than it seems. Non-terminals are defined by names (like
|"Expr"|). Note that we are using a promoted string here, the kind |Symbol| in
modern Haskell. Productions are also identified by a name, and are related to a
non-terminal. Children are once more names, tied to a production and either a
non-terminal or a terminal. Everything is wrapped on constructors of simple
algebraic data kinds, since we implement everything strongly typed both at term
level, and at type level. |Label| is actually a |Proxy| with an alternative name
adecuated to our domain. Everything is defined at type level but we will use
this proxies as carriers of type information. A widely used idiom in type level
programming.

To define semantics for evaluation we can use two atributes: one to represent
the result of the evaluation (that is certanly synthesized), and one to distribute
the context defining semantics for variables.

> eval = Label @ ('Att "eval" Int)
> env  = Label @ ('Att "env"  (Map String Int))


\todo{If the user wants, all this code could be derived using ...

< deriveAG ..
< attLabels
}

Time to define semantics:

> add_eval   =  syndefM eval add
>            $ (+) <$> at leftAdd eval <*> at rightAdd eval

> val_eval   =  syndefM eval val
>            $ ter ival

> var_eval   =  syndefM eval var
>            $ slookup <$> ter vname <*> at lhs env
>   where slookup nm = fromJust . Data.Map.lookup nm
