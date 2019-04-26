%
% The first command in your LaTeX source must be the \documentclass command.
\documentclass[sigconf]{acmart}

%
% \BibTeX command to typeset BibTeX logo in the docs
\AtBeginDocument{%
  \providecommand\BibTeX{{%
    \normalfont B\kern-0.5em{\scshape i\kern-0.25em b}\kern-0.8em\TeX}}}

% Rights management information. 
% This information is sent to you when you complete the rights form.
% These commands have SAMPLE values in them; it is your responsibility as an author to replace
% the commands and values with those provided to you when you complete the rights form.
%
% These commands are for a PROCEEDINGS abstract or paper.
\copyrightyear{2019}
\acmYear{2019}
\setcopyright{acmlicensed}
\acmConference[Woodstock '18]{Woodstock '18: ACM Symposium on Neural Gaze Detection}{June 03--05, 2018}{Woodstock, NY}
\acmBooktitle{Woodstock '18: ACM Symposium on Neural Gaze Detection, June 03--05, 2018, Woodstock, NY}
\acmPrice{15.00}
\acmDOI{10.1145/1122445.1122456}
\acmISBN{978-1-4503-9999-9/18/06}

%
% These commands are for a JOURNAL article.
%\setcopyright{acmcopyright}
%\acmJournal{TOG}
%\acmYear{2018}\acmVolume{37}\acmNumber{4}\acmArticle{111}\acmMonth{8}
%\acmDOI{10.1145/1122445.1122456}

%
% Submission ID. 
% Use this when submitting an article to a sponsored event. You'll receive a unique submission ID from the organizers
% of the event, and this ID should be used as the parameter to this command.
%\acmSubmissionID{123-A56-BU3}

%
% The majority of ACM publications use numbered citations and references. If you are preparing content for an event
% sponsored by ACM SIGGRAPH, you must use the "author year" style of citations and references. Uncommenting
% the next command will enable that style.
%\citestyle{acmauthoryear}

%
% end of the preamble, start of the body of the document source.

\usepackage[utf8]{inputenc}

\usepackage {amssymb}

%include polycode.fmt
\setlength{\mathindent}{0.3cm}

\begin{document}
%
% The "title" command has an optional parameter, allowing the author to define a "short title" to be used in page headers.
\title{First Class Strongly Kinded Attribute Grammars}

%
% The "author" command and its associated commands are used to define the authors and their affiliations.
% Of note is the shared affiliation of the first two authors, and the "authornote" and "authornotemark" commands
% used to denote shared contribution to the research.
\author{Juan García Garland}


\affiliation{%
  \institution{Instituto de Computación}
  \streetaddress{P.O. Box 1212}
  \city{Montevideo}
  \state{Uruguay}
  \postcode{43017-6221}
}
\author{Alberto Pardo}


\affiliation{%
  \institution{Instituto de Computación}
  \streetaddress{P.O. Box 1212}
  \city{Montevideo}
  \state{Uruguay}
  \postcode{43017-6221}
}\author{Marcos Viera}


\affiliation{%
  \institution{Instituto de Computación}
  \streetaddress{P.O. Box 1212}
  \city{Montevideo}
  \state{Uruguay}
  \postcode{43017-6221}
}

%
% By default, the full list of authors will be used in the page headers. Often, this list is too long, and will overlap
% other information printed in the page headers. This command allows the author to define a more concise list
% of authors' names for this purpose.
\newcommand{\lipsum}{Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum}

\newcommand{\longlipsum}{ Proin ut ex sodales, vulputate orci id, finibus mi. Fusce at mauris nisi. Integer sapien turpis, pulvinar eu consectetur eu, ultrices non erat. Morbi pharetra ex mi, nec tristique felis interdum pellentesque. Sed at congue ante. Nulla sed aliquet quam, at ornare orci. Curabitur dictum mauris id mauris euismod gravida.

Nunc commodo dui sit amet orci aliquet, eget aliquet dui mollis. Quisque imperdiet, dolor id hendrerit tempus, augue nisi euismod leo, nec pellentesque mi erat at nibh. Pellentesque lobortis sed leo eu aliquet. In eu libero quis libero volutpat tincidunt eu sodales nunc. Duis faucibus orci tellus. Aenean ornare magna eu molestie iaculis. Aenean lectus neque, pulvinar vel dapibus a, venenatis imperdiet metus. Nam vel purus auctor, convallis purus sit amet, luctus orci. Praesent nec arcu nulla. Cras vestibulum tincidunt erat et consectetur.

Curabitur et nisi eu risus placerat blandit quis eu purus. Sed aliquet, nunc dignissim accumsan sollicitudin, urna diam auctor velit, eu vulputate nunc neque ac mauris. Pellentesque molestie a nisl et ullamcorper. Maecenas quis auctor lorem. Duis sed condimentum erat. Nullam ac augue vitae augue hendrerit auctor. Nam sit amet tortor eget justo egestas elementum eu vel nisi. Etiam urna mauris, semper ac lectus ac, accumsan tincidunt est. Vestibulum a elementum est, dignissim lobortis turpis. Pellentesque habitant morbi tristique senectus et netus et malesuada fames ac turpis egestas. Class aptent taciti sociosqu ad litora torquent per conubia nostra, per inceptos himenaeos. Aliquam justo leo, interdum eleifend mi eu, consequat euismod libero. Sed ullamcorper ex sit amet magna efficitur, euismod ullamcorper risus fermentum. Donec nec pretium justo. Aenean gravida dolor nec ex lacinia, non tempus odio iaculis. }

%

% The abstract is a short summary of the work to be presented in the article.
\begin{abstract}
  \lipsum
\end{abstract}

%
% The code below is generated by the tool at http://dl.acm.org/ccs.cfm.
% Please copy and paste the code instead of the example below.
%
\begin{CCSXML}
<ccs2012>
 <concept>
  <concept_id>10010520.10010553.10010562</concept_id>
  <concept_desc>Computer systems organization~Embedded systems</concept_desc>
  <concept_significance>500</concept_significance>
 </concept>
 <concept>
  <concept_id>10010520.10010575.10010755</concept_id>
  <concept_desc>Computer systems organization~Redundancy</concept_desc>
  <concept_significance>300</concept_significance>
 </concept>
 <concept>
  <concept_id>10010520.10010553.10010554</concept_id>
  <concept_desc>Computer systems organization~Robotics</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
 <concept>
  <concept_id>10003033.10003083.10003095</concept_id>
  <concept_desc>Networks~Network reliability</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Computer systems organization~Embedded systems}
\ccsdesc[300]{Computer systems organization~Redundancy}
\ccsdesc{Computer systems organization~Robotics}
\ccsdesc[100]{Networks~Network reliability}

%
% Keywords. The author(s) should pick words that accurately describe the work being
% presented. Separate the keywords with commas.
\keywords{datasets, neural networks, gaze detection, text tagging}

%
% This command processes the author and affiliation and title information and builds
% the first part of the formatted document.
\maketitle


\newcommand{\todo}[1]{\fbox{
  \parbox{\textwidth/3}{TODO: \\ #1}}}
\newcommand{\note}[1]{\fbox{
  \parbox{\textwidth/3}{NOTE: \\ #1}}}

%format asp_sval    = "asp_{sval}"
%format p_Add       = "p_{Add}"
%format p_IntLit    = "p_{IntLit}"
%format p_VarLit    = "p_{VarLit}"
%format p_Let       = "p_{Let}"
%format sval_Add    = "sval_{Add}"
%format sval_IntLit = "sval_{IntLit}"
%format sval_VarLit = "sval_{VarLit}"
%format sval_Let    = "sval_{Let}"
%format .=.         = "\mathbin{\mathbf{\rightsquigarrow}}"
%format .*.         = ".\!\! * \!\! ."
%format ^           = " "
%format ^^          = "\;"
%format ::: = "\: `\! \! :"
%format € = "\: `("
%format forall = "\forall"
%format . = "."
%format .+. = "\oplus"
%format .++. = "\bigoplus"
%format .# = #
%format #. = #
%format Nil = "[]"
%format prom (a)  = "\: `" a " "
%format (prom(a)) = "\: `" a " "
%format EmpK      = "\: `[]"

\section{Introduction}

\section{EDSL usage example}

Let's define a simple language for arithmetic expressions with binders.
To keep it simple we use only one operator. We can represent expressions
as |let x = 3 + 4 in x + 4| (which denotes the integer 11).
The abstract syntax tree for such a language can be implemented in Haskell
as:
  
> data Exp
>   =  Add      {  l, r  :: Exp     }
>   |  Let      {  vLet  :: String, vDef, letExp :: Exp}
>   |  IntLit   {  i     :: Int     }
>   |  VarLit   {  v     :: String  }

%if False

>   deriving Show

%endif

\todo{
from the grammar perspective there is a non terminal, four productions..
}

The use of named fields is intentional, to use this names at compile time
to generate some boilerplate code with Template Haskell\cite{Sheard:2002:TMH:636517.636528}.
To do that, the library provides a function |deriveAG|.

> $(deriveAG '' Exp)

\todo{
hablar del codigo generado, dado que mas adelante se usan las
etiquetas
}

This provides the implementation of |sem_Exp|, the semantic function that
given a combination of aspects (which is also an aspect),
it provides the computation for the semantics given. And a set
of Labels which are used to name productions and non-terminals, 
both at type level, and at value level.

> data P_IntLit
> p_IntLit :: Label P_IntLit

The former example expression |let x = 3 + 4 in x + 4|

> e_1 = Let "x"  (Add  (IntLit 3)
>                      (IntLit 4))
>                (Add  (VarLit  "x")
>                      (IntLit  4  ))


\todo{
la semantica usa dos atributos, motivarlo
}

> $(attLabels ["sval", "ienv"])

Aspects are defined in our EDSL as records that represent mappings
from productions to rules. The |.=.| operator is used to tag rules
given a label. For the inherited attribute |asp_sval| can be defined
this way:

> asp_sval  =    ^^ p_Add     .=. sval_Add
>           .*.  ^^ p_IntLit  .=. sval_IntLit
>           .*.  ^^ p_VarLit  .=. sval_VarLit
>           .*.  ^^ p_Let     .=. sval_Let
>           .*.  ^^ emptyRecord

where |sval_Add|, |sval_IntList|, |sval_VarLit| and |sval_LEt| are rules.
Rules are actually functions from the inherited attributes of the parent,
and the synthesized attributes of the children (input family) to the
..... \todo{..}
We define rules using some predefined functions. The function |syndef|
adds a synthesized attribute:

> sval_Add
>  = \fam -> syndef sval $
>     chi fam .# ch_l #. sval + chi fam .# ch_r #. sval

> sval_IntLit
>  = \fam -> syndef sval $
>     chi fam .# ch_i #. lit @ Int

> sval_VarLit
>  = \fam -> syndef sval $
>   let env  = par fam #. ienv
>       li   = chi fam .# ch_v #. lit @ String
>   in case M.lookup li env of
>        Just a -> a

> sval_Let
>  = \fam -> syndef sval $
>     chi fam .# ch_i #. lit @ Integer

\todo{hablar de la definicion del syn}


> asp_ienv =
>       p_Add  .=. copy ienv (nt_Exp .: HNil)
>  .*.  p_Let  .=. (\fam ->
>         let vDef   = chi fam .# ch_vDef #. sval
>             name   = chi fam .# ch_vLet #. lit @ String
>         in inhdef ienv (nt_Exp .: HNil)
>             (   ch_letExp  .=. (M.insert name vDef (par fam #. ienv))
>            .*.  ch_vDef    .=. (par fam #. ienv)
>            .*.  emptyRecord))
>  .*. emptyRecord


\todo{llamada}


\subsection{Adding attributes}

\todo{nuevos atributos}

\subsection{Grammar extension}

\todo{extensión de gramática??}


\subsection{Domain specific Type Errors}

\todo{type errors}


\cite{Viera:2009:AGF:1596550.1596586}

\section{Strongly typed Heterogeneous collections}


\subsection{Heterogeneous Lists in Haskell}
\todo{hlist?}

\subsection{strongly typed heterogeneous records}

\todo{la idea aca es que sea breve, ya el código es una masa,
hay que ver}


> data Record :: forall k . [(k,Type)] -> Type where
>   EmptyR  :: Record  EmpK
>   ConsR   :: LabelSet ( prom( (l, v) ) ::: xs) =>
>      Tagged l v -> Record xs -> Record ( prom((l,v)) ::: xs)


\note{explicar predicado}

> class LabelSet (l :: [(k1,k2)])

> instance LabelSet []

> instance  LabelSet [(x,v)] 
> instance  LabelSet' (l1,v1) (l2,v2) (l1==l2) r
>       =>  LabelSet ( (l1,v1) ::: (l2,v2) ::: r)

> class LabelSet' l1v1 l2v2 (leq::Bool) r
> instance  (   LabelSet ( (l2,v2) ::: r)
>           ,   LabelSet ( (l1,v1) ::: r))
>           =>  LabelSet' (l1,v1) (l2,v2) False r



\note{un ejemplo de función}
\begin{code}

class HasFieldRec (l::k) (r :: [(k,Type)]) where
  type LookupByLabelRec l r :: Type
  lookupByLabelRec:: Label l -> Record r -> LookupByLabelRec l r


instance (HasFieldRec' (l == l2) l ( (l2,v) ::: r)) =>
  HasFieldRec l ( (l2,v) ::: r) where
  type LookupByLabelRec l ( (l2,v) ::: r)
    = LookupByLabelRec' (l == l2) l ( (l2,v) ::: r)
  lookupByLabelRec :: Label l -> Record ( (l2,v) ::: r)
                    -> LookupByLabelRec l ( (l2,v) ::: r)
  lookupByLabelRec l r
    = lookupByLabelRec' (Proxy :: Proxy (l == l2)) l r 

class HasFieldRec' (b::Bool) (l::k) (r :: [(k,Type)]) where
  type LookupByLabelRec' b l r :: Type
  lookupByLabelRec' ::
     Proxy b -> Label l -> Record r -> LookupByLabelRec' b l r

infixl 3 .#.
(.#.)  :: (HasFieldRec l r)
   => Record r -> Label l -> (LookupByLabelRec l r)
c .#. l = lookupByLabelRec l c

instance HasFieldRec'    True l ( (l, v) ::: r) where
  type LookupByLabelRec' True l ( (l, v) ::: r) = v
  lookupByLabelRec' _ _ (ConsR lv _) = unTagged lv

instance (HasFieldRec l r )=>
  HasFieldRec' 'False l ( (l2, v) : r) where
  type LookupByLabelRec' False l ( (l2, v) ::: r) = LookupByLabelRec l r
  lookupByLabelRec' _ l (ConsR _ r) = lookupByLabelRec l r

\end{code}


\note{un ejemplo de resultado que se usa solo en compilación}

> class HasLabelRec (e :: k)(r ::[(k,Type)]) where
>   type HasLabelRecRes (e::k)(r ::[(k,Type)]) :: Bool
>   hasLabelRec :: Label e -> Record r -> Proxy (HasLabelRecRes e r)

> instance HasLabelRec e   [] where
>   type HasLabelRecRes e  [] = False
>   hasLabelRec _ _ = Proxy

> instance HasLabelRec  k ( (k' ,v) ::: ls) where
>   type HasLabelRecRes k ( (k' ,v) ::: ls)
>       = Or (k == k') (HasLabelRecRes k ls)
>   hasLabelRec _ _ = Proxy


\section{Design and implementation of AspectAG}

\note{}
\subsection{Families}


\todo{uso de records en varios contextos, lo que lleva a:}

\subsection{Generic Records}


> data Fam  (c  :: [((k, Type),[(k,Type)])])  ^
>           (p  :: [(k,Type)])                :: Type
>  where
>   Fam  ::  ChAttsRec c
>        ->  Attribution p
>        ->  Fam c p


> type Rule  (sc   :: [((k,Type), [(k, Type)])])
>            (ip   :: [(k,       Type)])
>            (ic   :: [((k,Type), [(k, Type)])])
>            (sp   :: [(k,       Type)])
>            (ic'  :: [((k,Type), [(k, Type)])])
>            (sp'  :: [(k,       Type)])
>   = Fam sc ip -> Fam ic sp -> Fam ic' sp'

> ext  ::  Rule sc ip ic sp ic' sp'
>      ->  (Fam sc ip -> a -> Fam ic sp)
>      ->  (Fam sc ip -> a -> Fam ic' sp')
> (f `ext` g) input = f input . g input



\subsection{Primitives to declare rules}

> syndef :: LabelSet ( '(att,val) ': sp)
>  => Label att -> val
>  -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
> syndef latt val (Fam ic sp)
>   = Fam ic (latt =. val *. sp)

\begin{code}

inhdef :: Defs att nts vals ic
  => Label att -> HList nts -> Record vals
  -> (Fam ic sp -> Fam (DefsR att nts vals ic) sp)
inhdef att nts vals (Fam ic sp) = Fam (defs att nts vals ic) sp



class SingleDef  (mch::Bool) (mnts::Bool)
                 att pv
                 (ic ::[((k,Type),[(k,Type)])])
 where
  type SingleDefR mch mnts att pv ic :: [((k,Type),[(k,Type)])]
  singledef  :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
             -> ChAttsRec (SingleDefR mch mnts att pv ic)


             
instance  (  HasChildF lch ic
          ,  och ~ LookupByChildFR lch ic
          ,  UpdateAtChildF lch ( (att,vch) ::: och) ic
          ,  LabelSet ( (att, vch) ::: och))
        =>  SingleDef True True att (Tagged lch vch) ic
 where
  type SingleDefR True True att (Tagged lch vch) ic
    = UpdateAtChildFR lch ( (att,vch) ::: (LookupByChildFR lch ic)) ic
  singledef _ _ att pch ic
    = updateAtChildF (Label :: Label lch) ( att =. vch *. och) ic
    where lch = labelTChAtt pch
          vch = unTaggedChAtt pch
          och = lookupByChildF lch ic

instance (TypeError (Text "TypeError: Undefined non terminal."
                :$$: Text "In some definition of an INHERITED attribute "
                :$$: Text "there is a children associated to a non-terminal: "
                :<>: ShowType t
                :$$: Text "for which the attribute is not being declared."),
          pv ~ Tagged (lch, t) vch
          )
  => SingleDef True False att pv ic where
  type SingleDefR True False att pv ic = []
  singledef = undefined

\end{code}

\subsection{combination of Aspects}










\bibliographystyle{ACM-Reference-Format}
\bibliography{bib}

% 
% If your work has an appendix, this is the place to put it.
\appendix


\end{document}
