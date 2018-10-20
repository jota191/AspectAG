\subsection{Gram\'aticas de atributos} 

Las gram\'aticas de atributos~\cite{Knuth68semanticsof}
son un formalismo para describir computaciones
recursivas sobre tipos de datos. Dada una gramática libre de contexto,
se le asocia una sem\'antica considerando atributos en cada producci\'on,
que toman valores que son calculados mediante reglas a partir de los valores
de los atributos de los padres y de los hijos del arbol de sintaxis abstracta.

Los atributos se dividen cl\'asicamente en dos grupos: heredados y sintetizados.
Los atributos heredados son "pasados" como un contexto desde los padres a los
hijos. Los atributos sintetizados son calculados seg\'un las reglas
sem\'anticas,
en funci\'on de los atributos de los hijos (y eventualmente de los padres). 

Las gram\'aticas de atributos son especialmente interesantes
para la implementaci\'on de compiladores [REF UHC, libro del dragon?],
traduciendo el arbol sint\'actico directamente en alg\'un lenguaje de
destino o representaci\'on intermedia. Tambi\'en es posible validar chequeos
sem\'anticos de reglas que no est\'an presentes sint\'acticamente
(por ejemplo compilando lenguajes con sintaxis no libre de contexto,
parseados previamente seg\'un una gram\'atica libre de contexto
como la mayor\'ia de los languajes de programaci\'on modernos), o para realizar
chequeos de tipos.

Las gram\'aticas de atributos son \'utiles en s\'i mismas como un paradigma de
programaci\'on, y significan una soluci\'on a un
conocido t\'opico de discusi\'on en la comunidad
llamado "El problema de la expresi\'on"
("The expression problem", t\'ermino acu\~nado por P. Wadler
~\cite{ExpressionProblem}).
Cuando el software se construye de manera incremental es deseable que sea
sencillo introducir nuevos tipos de datos
o enriquecer los existentes, y tambi\'en que sea simple
implementar nuevas operaciones. Normalmente dise\~nar un lenguaje pensando en
una de las utilidades va en desmedro de la otra, siendo la programaci\'on
orientada objetos el ejemplo paradigm\'atico de t\'ecnica orientada a los
datos, y la programaci\'on funcional,
por el contrario el ejemplo donde es simple
agregar funciones, siendo costoso en cada paradigma hacer lo dual (pensar en
cuan complicado (y cuantos m\'odulos hay que modificar)
es agregar un m\'etodo en una estructura de clases amplia,
o cuantas funciones hay que modificar en los lenguajes funcionales
si en un tipo algebr\'aico se agrega una construcci\'on).

Las gram\'aticas de atributos son una propuesta de soluci\'on a este
problema, deber\'ia ser simple agregar nuevas producciones
(definiendo \emph{localmente} las reglas de computaci\'on de los atributos
existentes sobre el nuevo caso, as\'i como agregar
nuevas funcionalidades (definiendo \emph{localmente}
nuevos atributos con sus reglas, o bien combinando los ya existentes).

Por sus caracter\'isticas, donde las computaciones se expresan de forma local
en cada producci\'on combinando c\'omo la informaci\'on fluye de arriba a abajo
y de abajo a arriba, una aplicaci\'on \'util de las AGs es la de definir
computaciones circulares. En la pr\'oxima secci\'on introducimos
un caso de estudio.
[HABLAR DE ASPECTOS]


\subsection{Ejemplo: {\tt repmin}}

Como ejemplo consideramos la cl\'asica funci\'on {\tt repmin}
~\cite{birdRepmin}, que dado un \'arbol de enteros
(por ejemplo con la informaci\'on en las hojas), retorna un \'arbol con la
misma topolog\'ia, conteniendo el menor valor del \'arbol original en cada
hoja.
Consideramos la siguiente estructura en haskell para representar el \'arbol:
\footnote{explicar por que marcamos la raiz}

> data Root = Root Tree deriving Show

> data Tree = Node Tree Tree
>           | Leaf Int
>           deriving Show


La funci\'on {\tt repmin} puede definirse como sigue:

> repmin = sem_root

> sem_root :: Root -> Tree
> sem_root (Root tree)
>   = let (smin,sres) = (sem_Tree tree) smin
>     in sres

> sem_Tree :: Tree -> Int -> (Int, Tree)
> sem_Tree (Node l r)
>   = \ival -> let (lmin,lres) = (sem_Tree l) ival
>                  (rmin,rres) = (sem_Tree r) ival
>              in (lmin `min` rmin, Node lres rres )

> sem_Tree (Leaf i)
>   = \ival -> (i, Leaf ival)


Por otra parte, una
definici\'on por gram\'aticas de atributos viene dada de la
siguinte manera:


\begin{center}
\includegraphics[width=8cm]{./src/img/ag-repmin.png}
\end{center}

Nuevamente tenemos un \'arbol con ra\'iz expl\'icita.
La raz\'on para tomar \'esta decisi\'on de dise\~no es tener
un s\'imbolo de inicio expl\'icito de la gram\'atica. A nivel
operacional nos va a permitir saber cuando encadenar atributos
sintetizados con heredados.

La palabra clave {\tt SYN} introduce un atributo sintetizado.
{\tt smin} y {\tt sres} son atributos sintetizdos de tipo
{\tt Int} y {\tt Tree} respectivamente.
Las sem\'anticas de cada uno se definen luego de la sentencia
{\tt SEM}. {\tt smin} representa en cada producci\'on el
m\'inimo valor de una hoja en el sub\'arbol correspondiente,
calculandose en las hojas como el valor que contiene
(que, formalmente puede considerarse un nuevo atributo, impl\'icito),
y en los nodos como una funci\'on (el m\'inimo) del valor del
mismo atributo {\tt smin} en los sub\'arboles.

{\tt sres} en cada producci\'on vale un \'arbol con la misma forma
que el sub\'arbol original, con el m\'inimo global en cada hoja.
En la ra\'iz se copia el sub\'arbol, en cada nodo se construye
un nodo con los sub\'arboles que contiene el atributo {\tt sres}
en los sub\'arboles. En las hojas se calcula en funci\'on del
atributo heredado {\tt ival}.

Los atributos heredados se definen con la sentencia {\tt INH}.
En el ejemplo {\tt ival} es el \'unico atributo heredado,
que representa el valor m\'inimo global en el \'arbol.

En la ra\'iz, {\tt ival} se computa como una copia del valor
{\tt smin}. Se aprecia por qu\'e necesitabamos marcar la ra\'iz del
\'arbol: para saber cuando copiar.
En los nodos, a cada sub\'arbol se le copia el valor de ival actual.

\subsection{AspectAG}

La implementaci\'on sige a grandes razgos la siguiente idea:

En cada producci\'on, llamamos \emph{atribuci\'on} (Attribution)
al registro de todos los atributos. Una atribuci\'on ser\'a un mapeo
de nombres de atributos a sus valores. Los nombres de atributos
se manejan en tiempos de compilaci\'on, por lo que una estructura
como la presentada en la secci\'on[REF] es adecuada.
En cada nodo, una regla sem\'antica consiste en un mapeo de
una input family a una output family [definirlas]


Presentamos una soluci\'on al problema {\tt repmin}
en la reimplementaci\'on del EDSL, para que el lector tome contacto
con el estilo de programaci\'on en el EDSL. Luego se presentar\'a
mayor detalle.

Hay que definir m\'ultiples \emph{Etiquetas}.
Hay etiquetas para los no terminales, para los atributos, y para nombrar a los
hijos en cada producci\'on. Por ejemplo, para los atributos:

> data Att_smin; smin = Label :: Label Att_smin
> data Att_ival; ival = Label :: Label Att_ival
> data Att_sres; sres = Label :: Label Att_sres

Las etiquetas existen solo a nivel de tipos([REF phantom types]),
{\tt Label} es una implementaci\'on especializada de {\tt Proxy}.
En nuestra implementaci\'on todos
los Records extensibles son polim\'orficos en el kind de los \'indices, por
lo cual es posible definir tipos de datos para cada tipo de etiqueta
y utilizar el kind promovido.


Def\'inanse las reglas para el atributo {\tt smin}.
Notar en la especificaci\'on de la gram\'atica de atributos
que tiene reglas de computaci\'on en el \'arbol, por lo que hay dos
producciones (Node y Leaf). 
En AspectAG:

> node_smin (Fam chi par)
>   = syndef smin $ (chi # ch_l # smin) `min` (chi # ch_r # smin)

> leaf_smin (Fam chi par)
>   = syndef smin $ chi # ch_i # leafVal

Informalmente, para el nodo se define un atributo {\tt smin}, que se
calcula como el m\'inimo entre el valor de {\tt smin} del hijo {\tt ch\_l}
(nombre del hijo izquierdo), y el valor de {\tt smin} del hijo {\tt ch\_r}.
En el caso de la hoja, se toma el valor de leafVal (que es un nombre para
el valor guardado), para el (unico) hijo en la producci\'on {\tt ch\_i}.
Si bien todos los terminales van a tener un \'unico hijo con su valor,
implementar fuertemente tipado nos obliga a respetar esta estructura
(o complicar mucho la implementaci\'on).


Notar que lo que definimos son en realidad funciones: un mapeo de la
\emph{input family} (atributos heredados del padre y sintetizados de los hijos)
a la \emph{output family} (sintetizados del padre, heredados a los hijos).
Los valores de arriba tienen tipo \emph{Rule} [RFRENCIA MAS ADELANTE].

An\'alogamente se define el atributo heredado {\tt sres}:

> root_sres (Fam chi par)
>   = syndef sres $ chi # ch_tree # sres

> node_sres (Fam chi par)
>   = syndef sres $ Node (chi # ch_l # sres)(chi # ch_r # sres)

> leaf_sres (Fam chi par)
>   = syndef sres $ Leaf (par # ival)

Notar que est\'a definido para la ra\'iz, y que en la hoja usamos un atributo
sintetizado para computar.

Por \'ultimo presentamos el atributo sintetizado:


> root_ival (Fam chi par) =
>   inhdef ival [nt_Tree] ( ch_tree .=.(chi # ch_tree # smin)
>                        .*. emptyRecord)
  
> node_ival (Fam chi par) =
>   inhdef ival [nt_Tree] (  ch_l .=. par # ival
>                        .*. ch_r .=. par # ival
>                        .*. emptyRecord)

Informalmente, declaramos que se define un atributo heredado llamado
{\tt ival}, y se declara un registro donde se especifica para cada hijo
c\'omo se computar\'a {\tt ival}.
El par\'ametro extra {\tt [nt\_Tree]} es una lista de no terminales,
por ahora no le damos importancia.

Los \emph{aspectos} se definen como un registro con las reglas para
cada producci\'on:


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

Que pueden combinarse mediante el operador {\tt .+.}:

> asp_repmin = asp_smin .+. asp_sres .+. asp_ival

Finalmente {\tt repmin : Tree -> Tree } viene dado por:

> repmin t = sem_Root asp_repmin (Root t) emptyAtt # sres

En donde {\tt sem\_Root} es una funci\'on definida una sola vez.

