\subsection{Gram\'aticas de atributos} 

Las gram\'aticas de atributos (AGs)~\cite{Knuth68semanticsof}
son un formalismo para describir computaciones
recursivas sobre tipos de datos\footnote{Tipos de datos algebr\'aicos
o gram\'aticas son formalismos equivalentes}.
Dada una gram\'atica libre de contexto
se le asocia una sem\'antica considerando \emph{atributos}
en cada producci\'on,
los cuales toman valores calculados mediante reglas a partir de los valores
de los atributos de los padres y de los hijos en el
\'arbol de sintaxis abstracta.
Los atributos se dividen cl\'asicamente en dos tipos:
heredados y sintetizados.
Los atributos heredados son pasados como contexto desde los padres a los
hijos. Los atributos sintetizados, por el contrario fluyen ``hacia arriba''
en la gram\'atica, propag\'andose desde los hijos de una producci\'on.
Un \emph{aspecto} es una colecci\'on de (uno o m\'as) aributos
y sus reglas de c\'omputo.

Las gram\'aticas de atributos son especialmente interesantes
en la implementaci\'on de
compiladores~\cite{Dijkstra:2009:AUH:1596638.1596650,Aho:1986:CPT:6448}
traduciendo el arbol de sintaxis abstracta en alg\'un lenguaje de
destino o representaci\'on intermedia. Tambi\'en es posible validar chequeos
sem\'anticos de reglas que no est\'an presentes sint\'acticamente
(por ejemplo compilando lenguajes con sintaxis no libre de contexto,
parseados previamente seg\'un una gram\'atica libre de contexto
como ocurre en la mayor\'ia de los languajes de programaci\'on modernos)
o implementar verificadores de tipos.

Adem\'as, las gram\'aticas de atributos
son \'utiles en si mismas como un paradigma de
programaci\'on.
Buena parte de la programaci\'on funcional consiste en
componer computaciones sobre \'arboles
(expresadas mediante \'algebras~\cite{Bird:1996:AP:256095.256116}, aplicadas
a un catamorfismo). Un
\'algebra en definitiva especifica una sem\'antica para una estructura
sint\'actica.
Cuando las estructuras de datos son complejas (por ejemplo, en la
representaci\'on del \'arbol
de sintaxis abstracta de un lenguaje de programaci\'on complejo),
surgen ciertas dificultades~\cite{Dijkstra:2009:AUH:1596638.1596650}.
Por ejemplo ante un cambio en la estructura
es necesario hacer cambios en la implementaci\'on del catamorfismo
y de todas las \'algebras.

M\'as en general la programaci\'on mediante gram\'aticas de atributos
significa una soluci\'on a un
conocido t\'opico de discusi\'on en la comunidad
llamado ``El problema de la expresi\'on''
(``The expression problem'', t\'ermino acu\~nado por
P. Wadler~\cite{ExpressionProblem}).
Cuando el software se construye de forma incremental es deseable que sea
sencillo introducir nuevos tipos de datos
o enriquecer los existentes con nuevos constructores,
y tambi\'en que sea simple implementar nuevas funciones.
Normalmente en el dise\~no de un lenguaje las decisiones que facilitan
una de las utilidades van en desmedro de la otra, siendo la programaci\'on
orientada objetos el ejemplo paradigm\'atico de t\'ecnica orientada a los
datos, y la programaci\'on funcional,
por el contrario el claro ejemplo donde es simple
agregar funciones, siendo costoso en cada paradigma hacer lo dual.
Pensar en cuan complicado (y cuantos m\'odulos hay que modificar,
y por tanto recompilar)
es agregar un m\'etodo en una estructura de clases amplia,
o cuantas funciones hay que modificar en los lenguajes funcionales
si en un tipo algebraico se agrega un constructor (y nuevamente,
cu\'antos m\'odulos se deben recompilar).

La \emph{Programaci\'on orientada a aspectos} mediante
gram\'aticas de atributos es una propuesta de soluci\'on a este
problema, donde es simple agregar nuevas producciones
(definiendo localmente las reglas de computaci\'on de los atributos
existentes sobre la nueva producci\'on, as\'i como agregar
nuevas funcionalidades (definiendo localmente
nuevos atributos con sus reglas, o bien combinando los ya existentes).

Por su caracter\'istica, donde las computaciones se expresan de forma local
en cada producci\'on combinando c\'omo la informaci\'on fluye
``de arriba a abajo''
y de ``abajo a arriba'', una aplicaci\'on \'util de las AGs es la de definir
computaciones circulares.

\newpage


\subsection{Ejemplo: {\tt repmin}}
\label{repmin}

Como ejemplo consideramos la cl\'asica funci\'on
{\tt repmin}~\cite{birdRepmin} que dado un \'arbol contenedor de enteros
(por ejemplo binario y con la informaci\'on en las hojas),
retorna un \'arbol con la
misma topolog\'ia, conteniendo el menor valor del \'arbol original en cada
hoja.
%% Consideramos la siguiente estructura en haskell para representar el \'arbol:


%% > data Root = Root Tree deriving Show

%% > data Tree = Node Tree Tree
%% >           | Leaf Int
%% >           deriving Show


%% Notar que utilizaremos la ra\'iz ``marcada'' con el tipo algebr\'aico
%% {\tt Root} en lugar de definir los \'arboles como es usual, donde la ra\'iz es
%% un nodo m\'as. Lo hacemos de esta manera para tener informaci\'on de
%% donde exactamente dejar de calcular el m\'inimo local, que ser\'a a partir de
%% ese punto global y comenzar a propagarlo a los hijos.

%% La funci\'on {\tt repmin} puede definirse como sigue:

%% > repmin = sem_root

%% > sem_root :: Root -> Tree
%% > sem_root (Root tree)
%% >   = let (smin,sres) = (sem_Tree tree) smin
%% >     in sres

%% > sem_Tree :: Tree -> Int -> (Int, Tree)
%% > sem_Tree (Node l r)
%% >   = \ival -> let (lmin,lres) = (sem_Tree l) ival
%% >                  (rmin,rres) = (sem_Tree r) ival
%% >              in (lmin `min` rmin, Node lres rres )

%% > sem_Tree (Leaf i)
%% >   = \ival -> (i, Leaf ival)


%% Por otra parte, una
%% definici\'on por gram\'aticas de atributos viene dada de la
%% siguinte manera:

%% \begin{center}
%% \includegraphics[width=8cm]{./src/img/ag-repmin.png}
%% \end{center}

%% Nuevamente tenemos un \'arbol con ra\'iz expl\'icita.
%% La raz\'on para tomar \'esta decisi\'on es una vez m\'as
%% tener un s\'imbolo de inicio expl\'icito de la gram\'atica, que a nivel
%% operacional nos va a permitir saber cuando encadenar atributos
%% sintetizados con heredados, aunque ahora la decisi\'on es m\'as natural;
%% la sem\'antica (i.e. c\'omo se computar\'an los
%% atributos) difiere en un nodo ordinario y en la ra\'iz.

Una definici\'on por gram\'aticas de atributos viene dada de la
siguiente manera:

\begin{center}
\includegraphics[width=8cm]{./src/img/ag-repmin.png}
\end{center}

Utilizamos la sintaxis de Utrecht[TODO:REF]
Las palabras clave {\tt DATA} introducen tipos de datos,
el ejemplo traducido a haskell corresponde a:

> data Root = Root Tree

> data Tree = Node { l, r :: Tree}
>           | Leaf {    i :: Int}


En lugar de utilizar el tipo {\tt Tree}
tanto para nodos internos como para la ra\'iz, como es usual,
utilizamos el tipo de datos {\tt Root} para `marcar` la ra\'iz del \'arbol
\'Esto es \'util para
tener un s\'imbolo de inicio expl\'icito de la gram\'atica, que a nivel
operacional nos va a permitir saber cuando encadenar atributos
sintetizados con heredados.
La decisi\'on es natural dado que la sem\'antica
(i.e. la forma en la que se computan los atributos)
difiere en un nodo ordinario y en la ra\'iz.


La palabra clave {\tt SYN} introduce un atributo sintetizado.
{\tt smin} y {\tt sres} son atributos sintetizados de tipo
{\tt Int} y {\tt Tree} respectivamente.
La sem\'antica de cada uno se define mediante de la sentencia
{\tt SEM}. {\tt smin} representa en el
m\'inimo valor de las hojas contenidas en el sub\'arbol correspondiente,
comput\'andose en las hojas como el valor que ellas contienen
(que, formalmente puede considerarse un nuevo atributo, impl\'icito),
y en los nodos el m\'inimo del valor del
mismo atributo {\tt smin} en los sub\'arboles.

El atributo {\tt sres} vale un \'arbol con la misma forma
que el sub\'arbol original pero con el m\'inimo global en cada hoja.
En la ra\'iz se copia el sub\'arbol, y en cada nodo iterno se construye
un nodo con los sub\'arboles que contiene el atributo {\tt sres}
en los sub\'arboles. En las hojas se calcula en funci\'on del
atributo heredado {\tt ival}.

Los atributos heredados se definen con la sentencia {\tt INH}.
En el ejemplo {\tt ival} es el \'unico atributo heredado,
que representa el valor m\'inimo global en el \'arbol.
En la ra\'iz, {\tt ival} se computa como una copia del valor
{\tt smin}. Se aprecia por qu\'e necesitabamos marcar la ra\'iz del
\'arbol: para saber cuando el m\'inimo local es global y computar {\tt ival}.
En los nodos, a cada sub\'arbol se le copia el valor de {\tt ival}
actual, que fluir\'a ``hacia abajo``.


\subsection{AspectAG}

AspectAG es un lenguaje de dominio espec\'ifico embebido en Haskell
que permite especificar gram\'aticas de atributos y utiliza programaci\'on
a nivel de tipos para que las gram\'aticas resultantes  
verifiquen est\'aticamente ciertas propiedades de buena formaci\'on.

La implementaci\'on sigue a grandes rasgos la siguiente idea:
Dada una estructura de datos sobre la que vamos a definir los atributos,
en cada producci\'on de la gram\'atica llamamos \emph{atribuci\'on}
al registro de todos los atributos. Una atribuci\'on es un mapeo
de nombres de atributos a sus valores. Los nombres de atributos
se manejan en tiempo de compilaci\'on, por lo que una estructura
como la presentada en la secci\'on \ref{hrecord}
es adecuada.
En cada producci\'on, la informaci\'on fluye de los atributos heredados del
padre y los sintetizados de los hijos, que se llaman en la literatura
``familia de entrada'' (\emph{input family}), a
los sintetizados del padre y heredados de los hijos, la \emph{output family}.
Una regla sem\'antica consiste en un mapeo de
una input family a una output family. 
Se le proveen al programador primitivas para definir atributos y sus reglas
sem\'anticas, que se agrupar\'an en \emph{aspectos}.
Se provee tambi\'en una primitiva
para combinar aspectos. Una funci\'on (la funci\'on sem\'antica)
se encarga de computar la AG, es decir, calcular el valor de los atributos
definidos en las producciones.

La especificaci\'on de una AG podr\'ia estar mal formada
(por ejemplo, al intentar usar atributos que no est\'an definidos para cierta
producci\'on). Como las atribuciones se conocen est\'aticamente,
los ejemplos mal formados ser\'an rechazados en tiempo de compilaci\'on.

Presentamos una soluci\'on al problema {\tt repmin}
en t\'erminos de nuestra reimplementaci\'on de AspectAG,
para que el lector tome contacto
con el estilo de programaci\'on en el EDSL. Luego se presentar\'a
mayor detalle de la implementaci\'on.

\label{labels}
Es necesario definir m\'ultiples tipos de \emph{Etiqueta}
\footnote{La biblioteca provee
funciones en TemplateHaskell para ahorrarnos el trabajo}.
Hay etiquetas para los s\'imbolos no terminales,
para los atributos, y para nombrar a los
hijos en cada producci\'on. Por ejemplo, para los atributos definimos:

> data Att_smin; smin = Label :: Label Att_smin
> data Att_ival; ival = Label :: Label Att_ival
> data Att_sres; sres = Label :: Label Att_sres


Las etiquetas tienen informaci\'on solo a nivel de tipos,
{\tt Label} es una implementaci\'on especializada de {\tt Proxy}.
  
> data Label (l :: k) = Label

N\'otese que en el ejemplo los tipos definidos para cada etiqueta son vac\'ios
(no tienen habitantes), su \'unica funci\'on es ser usados como par\'ametro en
{\tt Label}.

Veamos ahora las reglas para el atributo {\tt smin}.
En la especificaci\'on de la gram\'atica de atributos, puede observarse
que este atributo tiene reglas de computaci\'on en el \'arbol,
por lo que hay dos producciones donde hace falta definirlas
({\tt Node} y {\tt Leaf}). 
En AspectAG:

> node_smin (Fam chi par)
>   = syndef smin $ (chi # ch_l # smin) `min` (chi # ch_r # smin)

> leaf_smin (Fam chi par)
>   = syndef smin $ chi # ch_i # leafVal

Para comprender la definici\'on anterior
recordemos que las reglas son funciones, un mapeo de la
\emph{input family} (atributos heredados del padre y sintetizados de los hijos)
a la \emph{output family} (sintetizados del padre, heredados a los hijos).
El par\'ametro sobre el que se hace pattern matching ({\tt Fam chi par})
es entonces una familia, el campo {\tt chi} contiene el registro de los
hijos, con sus atribuciones, y el campo {\tt par} la atribuci\'on del padre.
Las funciones definidas tienen tipo {\tt Rule}. Los tipos
{\tt Fam} y {\tt Rule} se detallan en la secci\'on~\ref{reimpl}.


La definici\'on anterior expresa que para el nodo se define una regla para
el atributo sintetizado {\tt smin}, que se
calcula como el m\'inimo entre el valor de {\tt smin} del hijo {\tt ch\_l}
(nombre del hijo izquierdo), y el valor de {\tt smin} del hijo {\tt ch\_r}
(nombre del hijo derecho).
En el caso de la regla para la hoja, se toma el valor de {\tt leafVal}
(que es un nombre para
el valor guardado) para el (\'unico) hijo en la producci\'on {\tt ch\_i}.
Si bien generalmente los terminales van a tener un \'unico hijo con su valor
-parecen innecesarias dos etiquetas-
implementar de forma fuertemente tipada nos obliga a respetar esta estructura
(o complicar mucho la implementaci\'on). Todos los nombres
({\tt ch\_l}, {\tt ch\_r}, {\tt leafVal}, {\tt ch\_i})
son etiquetas definidas de forma an\'aloga a las etiquetas para atributos.

Notar que, adem\'as de los nombres, nada indica (a\'un) que las reglas
est\'en relacionadas a sus producciones.



An\'alogamente se definen las reglas para
el atributo sintetizado {\tt sres}:

> root_sres (Fam chi par)
>   = syndef sres $ chi # ch_tree # sres

> node_sres (Fam chi par)
>   = syndef sres $ Node (chi # ch_l # sres)(chi # ch_r # sres)

> leaf_sres (Fam chi par)
>   = syndef sres $ Leaf (par # ival)

En este caso el atributo estaba definido para la ra\'iz,
y en la hoja usamos un atributo
heredado {\tt ival} para computarle (el m\'inimo global).

Por \'ultimo presentamos el atributo heredado:

> root_ival (Fam chi par) =
>   inhdef ival [nt_Tree] $ ch_tree .=. chi # ch_tree # smin
>                        .*. emptyRecord
  
> node_ival (Fam chi par) =
>   inhdef ival [nt_Tree] $  ch_l .=. par # ival
>                        .*. ch_r .=. par # ival
>                        .*. emptyRecord

La funci\'on {\tt inhdef} requiere un registro donde se especifica
para cada hijo c\'omo se computar\'a {\tt ival}: desde la ra\'iz se
propaga el valor
del atributo sintetizado {\tt smin}, en los nodos del \'arbol se propaga
el valor de {\tt ival} tomado del padre, incambiado.
El par\'ametro extra {\tt [nt\_Tree]} es una lista de no terminales utilizada
para hacer ciertos chequeos est\'aticos, por ahora no le damos
importancia\footnote{\'este par\'ametro no es relevante para ninguna de las
funcionalidades que se implementaron en este proyecto, se incluye para
mantener la interfaz dado que ser\'a \'util cuando \'estas s\'i
se implementen en el futuro}.

Los aspectos se definen como un registro con las reglas para
cada producci\'on (aqu\'i es donde efectivamente asociamos a qu\'e
producci\'on se asocia cada regla).

\label{aspsres}

> asp_ival =  p_Root .=. root_ival
>         .*. p_Node .=. node_ival
>         .*. emptyRecord
> asp_sres =  p_Root .=. root_sres
>         .*. p_Node .=. node_sres
>         .*. p_Leaf .=. leaf_sres
>         .*. emptyRecord
> asp_smin =  p_Leaf .=. leaf_smin
>         .*. p_Node .=. node_smin
>         .*. emptyRecord

El operador {\tt (.*.)} permite construir regitros heterogeneos,
{\tt emptyRecord}
es el registro vac\'io. El operador {\tt (.=.)} construye campos del registro
dados un valor con el tipo de la etiqueta y su correspondiente regla.

Los aspectos pueden combinarse para formar uno nuevo
mediante el operador {\tt (.+.)}:

> asp_repmin = asp_smin .+. asp_sres .+. asp_ival

Finalmente {\tt repmin::Tree->Tree} viene dado por:

> repmin t = sem_Root asp_repmin (Root t) emptyAtt # sres

En donde {\tt sem\_Root} es la funci\'on sem\'antica,
una funci\'on definida una sola vez\footnote{La funci\'on sem\'antica
  es derivable a partir del functor de la estructura de datos.
  Al momento de la escritura de este documento el programador debe
  proveerla, pero es uno de los objetivos inmediatos de trabajo futuro
  automatizar la generaci\'on de la misma.}.


