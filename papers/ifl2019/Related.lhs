%Attribute grammars encoded in functional languages have a long history, starting
%with Johnson \cite{652508}. 
%Related to Haskell, the {\tt uuagc} (Uthrech University Attribute Grammar
%Compiler) is probably the most well known example. 


There is a significant number of AG implementations. Some of them are implemented
as standalone compilers or generators like LRC \cite{Saraiva02}, UUAGC
\cite{uuagc}, LISA \cite{lisa}, JastAdd \cite{jastadd} and Silver \cite{silver},
and others are embbeded in languages like Scala (e.g. Kiama \cite{kiama}) or Haskell
(\cite{DBLP:conf/gcse/MoorPW99, Moor99first-classattribute,
  Viera:2009:AGF:1596550.1596586,DBLP:conf/ifl/VieraBP18, MFS13,
  DBLP:phd/ethos/Balestrieri15}).
%
%
This work is based on \AspectAG\ \cite{Viera:2009:AGF:1596550.1596586}, where
extensible records are used to implement a strongly typed first class AG DSL
embedded in Haskell. By using new Haskell type level programming techniques we
obtain a more clear design and a safer implementation while preserving its main
characteristics.

Error messages were a big downside that we solved. Managing type errors on EDSLs
is an old problem and an active research area. The idea of transforming a typing
problem into a constraint problem is not new \cite{10635_42131,
  improvingtypeerror}. Other embedded implementations of AGs
\cite{DBLP:conf/ifl/VieraBP18} solve the type diagnose problem at the cost of
making it staged.

\begin{figure}[t]
  \centering
  \includesvg[width=0.4\textwidth]{./plot/bench}
  \vspace{-0.2in}
  \caption{Performance Comparison}
  \label{fig:bench}

  \vspace{-0.2in}
\end{figure}

We must say that the current version of the library introduces a performance
penalty compared to previous versions. It is expected an overhead in compilation
time since all type computations must be performed. This has not been tangibe to
us as library users. It is difficult to quantify this overhead since
old versions of \AspectAG\ do not compile in modern GHC. The big performance
downside is that all the new structures generate a runtime penalty. On the same
grammar we detected a big linear overhead as seen in Figure
\ref{fig:bench}. Performance was not our focus so this is
not alarming so far.

%First class implementations of Attibute grammars in Haskell were introduced by
%Moor \cite{Moor99first-classattribute} with a lightweight approach missing from
%type safety. Viera \emph{et al} \cite{Viera:2009:AGF:1596550.1596586} in the
%original design og \AspectAG\ introduced a type safe approach. Other embedded
%implementations existed \cite{DBLP:phd/ethos/Balestrieri15}. Error messages were
%a weakness. Also, we push a towards the direction of type safety making types
%strongly kinded. 



Compiler support added with the |TypeError| type family was essential, but further
support would be desirable, in particular to control class constraint solving
and to avoid leaks and non readable messages. Research by
Heeren~\cite{DBLP:phd/basesearch/Heeren05} was implemented for the Helium
compiler. Recently, Serrano Mena and Hage \cite{DBLP:phd/basesearch/Serrano18,
  DBLP:conf/ifl/SerranoH17} developed a set of techniques for customizing type
error diagnosis for GHC. We think this can complement our more ad-hoc approach.
%Unfortunately this implementation was not merged in main tree.






