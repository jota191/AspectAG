\usepackage{multicol}
\usepackage{color}
\usepackage{amsmath}
\usepackage{tikz}
\usetikzlibrary{arrows}
\usepackage{url}
\usepackage{xspace}
\usepackage{listings}

%include lhs2TeX.fmt

\lstdefinelanguage{oberon0}{
keywords={MODULE, END, PROCEDURE, VAR, TYPE, CONST, FOR, TO, WHILE, CASE, IF, BEGIN, ELSIF, ELSE, THEN, ARRAY, OF, RECORD, DO},
sensitive=true
}

\newcommand{\oberonsize}{\fontsize{10pt}{10pt}}
\lstnewenvironment{oberon0} {\lstset{language={oberon0}}\oberonsize}{}
\newcommand\textoberon[1]{{\lstinline[language={oberon0}]{#1}}}
\newcommand\textoberonF[1]{{\oberonsize\lstinline[language={oberon0}]{#1}}}

\lstset{
basicstyle=\small,
identifierstyle=\ttfamily,
keywordstyle=\ttfamily\bfseries,
commentstyle=\scriptsize\rmfamily,
basewidth={0.5em,0.5em},
fontadjust=true,
escapechar=~,
escapeinside={\%*}{*)}
}


\newcommand{\todo}[1]{%\error                uncomment to make sure there are no todos left
 \textcolor{blue}{\mbox{$^\ast$}}\marginpar{\raggedright
 \hspace{0pt}\sffamily\tiny{\sc \textcolor{blue}{todo:}}\\ \textcolor{blue}{#1}}}
%\newcommand{\doaitse}[1]{\textcolor{red}{\textbf{Doaitse:}#1}}
%\newcommand{\marcos}[1]{\textcolor{red}{\textbf{Marcos:}#1}}
\newcommand{\doaitse}[1]{%\error                uncomment to make sure there are no todos left
 \textcolor{red}{\mbox{$^\ast$}}\marginpar{\raggedright
 \hspace{0pt}\sffamily\tiny{\sc \textcolor{red}{doaitse:}}\\ \textcolor{red}{#1}}}
\newcommand{\marcos}[1]{%\error                uncomment to make sure there are no todos left
 \textcolor{red}{\mbox{$^\ast$}}\marginpar{\raggedright
 \hspace{0pt}\sffamily\tiny{\sc \textcolor{red}{marcos:}}\\ \textcolor{red}{#1}}}

\renewcommand{\doaitse}[1]{}
%\renewcommand{\marcos}[1]{}


\usepackage[ pdftex, pdfstartpage=1, baseurl=http://www.fing.edu.uy/~mviera
           , bookmarks, bookmarksnumbered, bookmarksopen=false
%%           , breaklinks, colorlinks
           , pdftitle={First Class Syntax, Semantics and Their Composition}
           , pdfsubject={}
           , pdfkeywords={haskell,attribute grammars, typed transformations, extensible languages, type-level programming}
           , pdfcreator={LaTeX with Lhs2TeX}
           , pdfproducer={pdflatex}
           , pdfauthor={Marcos Viera}
           , linkcolor=black
           , citecolor=black
           , filecolor=black
           , urlcolor=black
           ]{hyperref}

\newcommand{\ChristmasTree}{\texttt{ChristmasTree}\xspace}
\newcommand{\AspectAG}{\texttt{AspectAG}\xspace}
\newcommand{\HList}{\texttt{HList}\xspace}
\newcommand{\murder}{\texttt{murder}\xspace}
\newcommand{\TTTAS}{\texttt{TTTAS}\xspace}
\newcommand{\uulib}{\texttt{uulib}\xspace}
\newcommand{\uuparsinglib}{\texttt{uu-parsinglib}\xspace}
\newcommand{\uuagc}{\texttt{uuagc}\xspace}
\newcommand{\languagec}{\texttt{language-c}\xspace}
\newcommand{\oberon}{\texttt{oberon0}\xspace}


\newcommand{\GHC}{\texttt{GHC}\xspace}
\newcommand{\UHC}{\texttt{UHC}\xspace}
\newcommand{\UUAGC}{\texttt{UUAGC}\xspace}


%format proc       = "\mathbf{proc}"
%format mdo        = "\mathbf{mdo}"
%format rec        = "\mathbf{rec}"
%format >>>        = "\mathbin{\text{\ttfamily{>>>}}}"
%%format <-        = "\mathbin{\text{\ttfamily{<-}}}"
%%format ->        = "\mathbin{\text{\ttfamily{->}}}"
%format -<         = "\prec{}"

%format  <*        = "\mathbin{\text{\small\ttfamily{<*}}}"
%format  <*>       = "\mathbin{\text{\small\ttfamily{<*>}}}"
%format  <**>      = "\mathbin{\text{\small\ttfamily{<**>}}}"
%format <??>       = "\mathbin{\text{\ttfamily{<??>}}}"
%format  <|>       = "\mathbin{\text{\small\ttfamily{<|>}}}"
%format  <$>       = "\mathbin{\text{\small\ttfamily{<\$>}}}"
%format  <$        = "\mathbin{\text{\small\ttfamily{<\$}}}"
%format  iI        = "\llfloor" 
%format  Ii        = "\rrfloor"

%format <.>  = "\mathbin{\text{\small\ttfamily{<.>}}}"
%format -->  = "\mathbin{\lhook\joinrel\relbar\joinrel\rightarrow}"
%format ~~>  = "\mathbin{\relbar\joinrel\leadsto}"
%format ==>  = "\mathbin{\Longrightarrow}"


%format >#<        = "\mathbin{\text{\small\ttfamily{>\#<}}}"
%format <#>        = "\mathbin{\text{\small\ttfamily{<\#>}}}"
%format  #>        = "\mathbin{\text{\small\ttfamily{ \#>}}}"
%format -#>        = "\mathbin{\text{\small\ttfamily{-\#>}}}"
%format <->        = "\mathbin{\text{\small\ttfamily{<->}}}"

%format  ^=        = "\mathbin{\mathbf{\in}}"
%format  ^|        = "\mathbin{\text{\ttfamily{\^{}|}}}"

%format  >|<       = "\mathbin{\text{\ttfamily{>|<}}}"
%format  <++>       = "\mathbin{\text{\small\ttfamily{<++>}}}"
%format  +>>        = "\mathbin{\text{\small\ttfamily{+>>}}}"

%format forall = "\forall"
%format exists = "\exists"

%format ^         = " "
%format ^^        = "\;"
%format DATA      = "\mathbf{DATA}"
%format ATTR      = "\mathbf{ATTR}"
%format INH       = "\mathbf{INH}"
%format SYN       = "\mathbf{SYN}"
%format SEM       = "\mathbf{SEM}"
%format USE       = "\mathbf{USE}"
%format EXTENDS   = "\mathbf{EXTENDS}"
%format lhs       = "\mathbf{lhs}"
%format lhs_      = "lhs"
%format .         = "."

%format ~         = "\mathbin{\;\sim\!}"
%format .*.       = "\mathbin{.\!\!*\!\!.}"
%format .=.       = "\mathbin{.\!\!=\!\!.}"
%format .+.       = "\mathbf{\;\oplus\;}"

%format .*..      = "\mathbin{.\!\!*\!\!..}"
%format .=..      = "\mathbin{.\!\!=\!\!..}"


%format bl_        = "\{"
%format el_        = "\}"

%format br_        = "\{\!\{"
%format er_        = "\}\!\}"

%format bra_        = "\{\!\{\!\{"
%format era_        = "\}\!\}\!\}"


%format \$ = "\;\$\;"

%% Template Haskell quotation
%format TH(a)      = $ ( a )
%format (THQ (a))  = "`" a
%format (THQQ (a)) = "``" a

%format exp1 = term
%format exp2 = factor

%format ntExp1 = ntTerm
%format ntExp2 = ntFactor

\setlength{\mathindent}{0.2cm}
