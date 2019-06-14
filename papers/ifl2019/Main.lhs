
%
% The first command in your LaTeX source must be the \documentclass command.
\documentclass[sigconf]{acmart}

\usepackage{fancyvrb}
\usepackage{bm}
%include polycode.fmt

%include myformat.fmt

\usepackage{ifthen}

%include lineno.fmt
\arrayhs

%
% \BibTeX command to typeset BibTeX logo in the docs
\AtBeginDocument{%
  \providecommand\BibTeX{{%
    \normalfont B\kern-0.5em{\scshape i\kern-0.25em b}\kern-0.8em\TeX}}}

% Rights management information. This information is sent to you when you
% complete the rights form. These commands have SAMPLE values in them; it is
% your responsibility as an author to replace the commands and values with those
% provided to you when you complete the rights form. These commands are for a
% PROCEEDINGS abstract or paper.
\acmConference[IFL'19]{International Symposium on Implementation and Application
  of Functional Languages}{September 2020}{Singapore} \acmYear{2020}
\copyrightyear{2020}

% These commands are for a JOURNAL article. \setcopyright{acmcopyright}
% \acmJournal{TOG}
% \acmYear{2018}\acmVolume{37}\acmNumber{4}\acmArticle{111}\acmMonth{8}
% \acmDOI{10.1145/1122445.1122456}

% Submission ID. Use this when submitting an article to a sponsored event.
% You'll receive a unique submission ID from the organizers of the event, and
% this ID should be used as the parameter to this command.
% \acmSubmissionID{123-A56-BU3}

% The majority of ACM publications use numbered citations and references. If you
% are preparing content for an event sponsored by ACM SIGGRAPH, you must use the
% "author year" style of citations and references. Uncommenting the next command
% will enable that style. \citestyle{acmauthoryear}

%
% end of the preamble, start of the body of the document source.

\usepackage[utf8]{inputenc}

\usepackage { amssymb }
\usepackage { hyperref }


\setlength{\mathindent}{0.3cm}

\begin{document}
% The "title" command has an optional parameter, allowing the author to define a
% "short title" to be used in page headers.
\title{Attribute Grammars Fly First-class... Safer!}
\subtitle{Dealing with DSL errors in type-level programming}

% The "author" command and its associated commands are used to define the
% authors and their affiliations. Of note is the shared affiliation of the first
% two authors, and the "authornote" and "authornotemark" commands used to denote
% shared contribution to the research.

\author{Juan García Garland}
\affiliation{%
  \institution{Instituto de Computación\\Universidad de la República}
  \streetaddress{P.O. Box 1212}
  \city{Montevideo}
  \state{Uruguay}
  \postcode{43017-6221}
}

\author{Alberto Pardo}
\affiliation{%
  \institution{Instituto de Computación\\Universidad de la República}
  \streetaddress{P.O. Box 1212}
  \city{Montevideo}
  \state{Uruguay}
  \postcode{43017-6221}
}


\author{Marcos Viera}
\affiliation{%
  \institution{Instituto de Computación\\Universidad de la República}
  \streetaddress{P.O. Box 1212}
  \city{Montevideo}
  \state{Uruguay}
  \postcode{43017-6221}
}

% By default, the full list of authors will be used in the page headers. Often,
% this list is too long, and will overlap other information printed in the page
% headers. This command allows the author to define a more concise list of
% authors' names for this purpose.
\newcommand{\lipsum}{Lorem ipsum dolor sit amet, consectetur adipiscing elit,
  sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad
  minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea
  commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit
  esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat
  non proident, sunt in culpa qui officia deserunt mollit anim id est laborum}

\newcommand{\longlipsum}{ Proin ut ex sodales, vulputate orci id, finibus mi.
  Fusce at mauris nisi. Integer sapien turpis, pulvinar eu consectetur eu,
  ultrices non erat. Morbi pharetra ex mi, nec tristique felis interdum
  pellentesque. Sed at congue ante. Nulla sed aliquet quam, at ornare orci.
  Curabitur dictum mauris id mauris euismod gravida.

Nunc commodo dui sit amet orci aliquet, eget aliquet dui mollis. Quisque
imperdiet, dolor id hendrerit tempus, augue nisi euismod leo, nec pellentesque
mi erat at nibh. Pellentesque lobortis sed leo eu aliquet. In eu libero quis
libero volutpat tincidunt eu sodales nunc. Duis faucibus orci tellus. Aenean
ornare magna eu molestie iaculis. Aenean lectus neque, pulvinar vel dapibus a,
venenatis imperdiet metus. Nam vel purus auctor, convallis purus sit amet,
luctus orci. Praesent nec arcu nulla. Cras vestibulum tincidunt erat et
consectetur.

Curabitur et nisi eu risus placerat blandit quis eu purus. Sed aliquet, nunc
dignissim accumsan sollicitudin, urna diam auctor velit, eu vulputate nunc neque
ac mauris. Pellentesque molestie a nisl et ullamcorper. Maecenas quis auctor
lorem. Duis sed condimentum erat. Nullam ac augue vitae augue hendrerit auctor.
Nam sit amet tortor eget justo egestas elementum eu vel nisi. Etiam urna mauris,
semper ac lectus ac, accumsan tincidunt est. Vestibulum a elementum est,
dignissim lobortis turpis. Pellentesque habitant morbi tristique senectus et
netus et malesuada fames ac turpis egestas. Class aptent taciti sociosqu ad
litora torquent per conubia nostra, per inceptos himenaeos. Aliquam justo leo,
interdum eleifend mi eu, consequat euismod libero. Sed ullamcorper ex sit amet
magna efficitur, euismod ullamcorper risus fermentum. Donec nec pretium justo.
Aenean gravida dolor nec ex lacinia, non tempus odio iaculis. }

%

% The abstract is a short summary of the work to be presented in the article.
\begin{abstract}
AspectAG is a domain specific language embedded in Haskell to represent modular
Attribute Grammars. In AspectAG attribute grammar fragments can be defined
independently (in separate modules) and then combined in a safe way. This
flexibility is achieved through the use of extensible records, which are
implemented as heterogeneous lists by using type-level programming techniques.
%; i.e. multi-parameter type classes and functional dependencies.

Type-level programming support has remarkably evolved in Haskell since the
first version of AspectAG was designed; having incorporated new features like
data promotion and kind polymorphism, among others, which allows to program in a
``strongly typed'' way at the level of types in a similar way as when
programming at the level of values.

In this paper we redefine AspectAG applying the new type-level programming
techniques. As a consequence, we obtain a more robust system with better error
messages.
\end{abstract}

%
% The code below is generated by the tool at http://dl.acm.org/ccs.cfm.
% Please copy and paste the code instead of the example below.
%
%% \begin{CCSXML}
%% % TODO
%% \end{CCSXML}

%% \ccsdesc[500]{Computer systems organization~Embedded systems}
%% \ccsdesc[300]{Computer systems organization~Redundancy}
%% \ccsdesc{Computer systems organization~Robotics}
%% \ccsdesc[100]{Networks~Network reliability}

% Keywords. The author(s) should pick words that accurately describe the work
% being presented. Separate the keywords with commas.
\keywords{Attribute Grammars, EDSL, Type Level Programming, Haskell}

% This command processes the author and affiliation and title information and
% builds the first part of the formatted document.
\maketitle


\newcommand{\todo}[1]{\fbox{
  \parbox{\textwidth/3}{TODO: \\ #1}}}
\newcommand{\note}[1]{\fbox{
  \parbox{\textwidth/3}{NOTE: \\ #1}}}
\newcommand{\marcos}[1]{\fbox{
  \parbox{\textwidth/3}{Marcos: \\ #1}}}

\newcommand{\AspectAG}{\texttt{AspectAG}}

\numbersoff

%% Introduction

%include Intro.lhs

%% Overview of teh library

%include OverviewLibrary.lhs

%%%%%%include ./ExprPaper.lhs

\section{Records and Requirements}

%include ./GenRecord.lhs

\section{Implementation}
\label{sec:aag}
%include ./AAG.lhs

\section{Related Work}
%include ./Related.lhs

\section{Conclusion and Future Work}
%include ./Conclusion.lhs

\bibliographystyle{ACM-Reference-Format}
\bibliography{bib}


\end{document}
