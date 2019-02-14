\subsection{Estructuras de Datos}
\label{reimpl}

Como se defini\'o antes,
una atribuci\'on (\emph{attribution}) es un mapeo de nombres de atributos
a sus valores, que representamos como un registro heterogeneo. A diferencia
de la implementaci\'on original, para obtener mensajes de error
precisos y evitar que se filtre
implementaci\'on en los mismos decidimos tener estructuras especializadas.

Un atributo (etiquetado por su nombre) viene dado por:

> newtype Attribute label value = Attribute value

que es el componente principal para construir atribuciones:

> data Attribution :: forall k . [(k,Type)] -> Type where
>   EmptyAtt :: Attribution '[]
>   ConsAtt  :: LabelSet ( '(att, val) ': atts) =>
>    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)

Notar que estamos utilizando todo el poder de las extensiones modernas.
Se utilizan kinds promovidos en las listas ({\tt DataKinds}),
polimorfismo en kinds en las etiquetas ({\tt PolyKinds}),
la estructura es un GADT ({\tt GADTs}), {\tt LabelSet} est\'a predicando sobre
un kind
polim\'orfico, donde usamos igualdad de kinds ({\tt ConstraintKinds}).

Una familia consiste en la atribuci\'on del padre y una colecci\'on
de atribuciones para los hijos etiquetadas por sus nombres.


> data Fam (c::[(k',[(k,Type)])]) (p :: [(k,Type)]) :: Type where
>   Fam :: ChAttsRec c  -> Attribution p -> Fam c p


La colecci\'on de atribuciones para los hijos se representan
de la siguiente manera:

> data ChAttsRec :: forall k k' . [(k , [(k',Type)])] -> Type where
>   EmptyCh :: ChAttsRec '[]
>   ConsCh  :: LabelSet ( '(l, v) ': xs) =>
>    TaggedChAttr chi att -> ChAttsRec chs -> ChAttsRec ( '(chi,att) ': chs)


La estructura es an\'aloga a la anterior: es de nuevo una implementaci\'on de
registro heterogeneo pero especializada.

Notar que en todos los tipos de datos definidos se expresa la estructura
en el nivel de los kinds. Por ejemplo, el primer par\'ametro
del constructor de tipos {\tt Fam}
debe ser un tipo de kind {\tt [(k',[(k,Type)])]}, lo cual modela
razonablemente un registro de registros (es un mapeo
con nombres de hijos como dominio, donde cada imagen contiene un nuevo mapeo
de atributos a valores). Luego a nivel de valores el constructor
{\tt Fam} requiere un primer argumento de tipo {\tt ChAttsRec c}, donde
{\tt c} ha de tener efectivamente el kind correcto. El kind no alcanza
para expresar que las listas de pares no repiten la primer componente,
para ello requerimos que se satisfaga la \emph{constraint}
{\tt LabelSet('(chi, att)':chs)}  en el constructor
de {\tt ChAttsRec}. Por supuesto, tambi\'en debemos asegurar
en tiempo de compilaci\'on que cada hijo contiene efectivamente una
atribuci\'on, por lo que {\tt TaggedChAttr} se define:

> data TaggedChAttr (l::k) (v :: [(k',Type)]) :: Type where
>   TaggedChAttr :: Label l -> Attribution v -> TaggedChAttr l v


De la misma forma podemos razonar sobre el segundo
par\'ametro de {\tt Fam}, a nivel de tipos tiene el kind {\tt [(k,Type)]},
a nivel de valores requerimos un habitante de {\tt Attribution p}, estructura
sobre la que chequeamos est\'aticamente que modele un mapeo.

En la implementaci\'on original no se expresaba ninguna informaci\'on a nivel
de los kinds.

\paragraph{Reglas} \hfill

Una regla es una funci\'on de la familia de entrada a la de salida.
Se implementa de la siguiente manera:
\label{rule}

> type Rule sc ip ic sp ic' sp'
>   = Fam sc ip -> (Fam ic sp -> Fam ic' sp')

El tipo contiene una aridad extra para hacer las reglas
componibles~\cite{Moor99first-classattribute}. Dada la familia
de entrada compuesta por atributos sintetizados de los hijos ({\tt sc})
y los heredados del padre ({\tt ip}),
se construye una funci\'on que toma como entrada
la familia de salida construida hasta el momento
(formada por los atributos heredados de los hijos ({\tt ic})
y los sintetizados por el padre ({\tt sp})), y la extiende (donde los nuevos
atributos heredados de los hijos son {\tt ic'} y los sintetizados por el padre
{\tt sp'}).

El kind de {\tt Rule} viene dado entonces por:

> Rule :: [(k', [(k, Type)])] -> [(k, Type)]
>      -> [(k', [(k, Type)])] -> [(k, Type)]
>      -> [(k', [(k, Type)])] -> [(k, Type)] -> Type


%% Para ser m\'as precisos, el tipo de rule podr\'ia declararse como:


%% > type Rule (sc  :: [(k', [(k, Type)])])
%% >           (ip  :: [(k,       Type)])
%% >           (ic  :: [(k', [(k, Type)])])
%% >           (sp  :: [(k,       Type)])
%% >           (ic' :: [(k', [(k, Type)])])
%% >           (sp' :: [(k,       Type)])
%% >   = Fam sc ip -> Fam ic sp -> Fam ic' sp'

Dos reglas construidas de esta forma se pueden componer:

> (f `ext` g) input = f input . g input


\subsection{Declaraci\'on de Reglas}

Se proveen distintas primitivas para declarar reglas.
En el ejemplo se utilizaron {\tt syndef} e {\tt inhdef}, que son
las m\'inimas adecuadas para tener un sistema utilizable.
En la implementaci\'on se proveen otras construcciones, y parte
del trabajo futuro pasa por codificar nuevas.

La primitiva {\tt syndef} provee la definici\'on de un nuevo
atributo sintetizado.
Dada una etiqueta no definida previamente que represente el
nombre del nuevo atributo a definir y un valor para el mismo, {\tt syndef}
construye una funci\'on que actualiza la familia que se ten\'ia
hasta el momento:

> syndef :: LabelSet ( '(att,val) ': sp) =>
>     Label att -> val -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
> syndef latt val (Fam ic sp) = Fam ic (latt =. val *. sp)

Los operadores {\tt (=.)} y {\tt (*.)} son azucar sint\'actica para
los constructores {\tt Attribute} y {\tt ConsAtt}, respectivamente.


Por otro lado
la funci\'on {\tt inhdef} introduce un atributo heredado
de nombre {\tt att} para una colecci\'on de no terminales {\tt nts}:

> inhdef :: Defs att nts vals ic ic' =>
>     Label att -> HList nts -> Record vals -> (Fam ic sp -> Fam ic' sp)
> inhdef att nts vals (Fam ic sp) = Fam (defs att nts vals ic) sp


{\tt vals} es un registro heterogeneo donde las etiquetas
representan los nombres de
los hijos, conteniendo valores que describen como computar el atributo
que est\'a siendo definido para cada uno de ellos.
En contraste con {\tt syndef}, es bastante m\'as compleja de implementar,
y para ello utilizamos la funci\'on auxiliar {\tt defs}, que inserta las
definiciones en los hijos a los que corresponda.


Para definir la funci\'on {\tt defs} se hace recursi\'on sobre
el registro {\tt vals} que contiene las nuevas definiciones. Se utiliza la
funci\'on auxiliar {\tt singledef} que inserta una \'unica definici\'on.
En la versi\'on original de la biblioteca esta funci\'on se
implementaba con dependencias funcionales en lugar de la familia de
tipos, y sin expresar informaci\'on en el kind.

> class Defs att (nts :: [Type])
>             (vals :: [(k,Type)]) (ic :: [(k',[(k,Type)])]) where
>   type DefsR att nts vals ic :: [(k',[(k,Type)])]
>   defs :: Label att -> HList nts -> Record vals -> ChAttsRec ic
>        -> ChAttsRec (DefsR att nts vals ic)


Si el registro est\'a vac\'io no se inserta ninguna definici\'on:

> instance Defs att nts '[] ic where
>   type DefsR att nts '[] ic = ic
>   defs _ _ _ ic = ic

En el caso recursivo, combinamos la primera componente del registro
con la llamada recursiva:

> instance ( Defs att nts vs ic
>          , ic' ~ DefsR att nts vs ic
>          , HMember t nts
>          , mnts ~ HMemberRes t nts
>          , HasLabelChildAtts (lch,t) ic'
>          , mch ~ HasLabelChildAttsRes (lch,t) ic'
>          , SingleDef mch mnts att (Tagged (lch,t) vch) ic') => 
>   Defs att nts ( '((lch,t), vch) ': vs) ic where
>   type DefsR att nts ( '((lch,t), vch) ': vs) ic
>     = SingleDefR (HasLabelChildAttsRes (lch,t) (DefsR att nts vs ic))
>                  (HMemberRes t nts)
>                  att
>                  (Tagged (lch,t) vch)
>                  (DefsR att nts vs ic)
>   defs att nts (ConsR pch vs) ic = singledef mch mnts att pch ic' 
>       where ic'  = defs att nts vs ic
>             lch  = labelLVPair pch
>             mch  = hasLabelChildAtts lch ic'
>             mnts = hMember (sndLabel lch) nts


Es decir, si la entrada es de la forma {\tt ConsR pch vs}, hacemos la llamada
recursiva con las dem\'as definiciones, guardando el resultado en {\tt ic'}.
La nueva definici\'on a insertar ({\tt pch}) ser\'a combinada
utilizando {\tt singleDef},
que adem\'as recibe como par\'ametros dos proxies que en su tipado transportan
la evidencia de la existencia de las etiquetas para el hijo y el no terminal
sobre el que estamos construyendo. Estos se obtienen mediante las llamadas
a {\tt hasLabelChilds} y {\tt hMember}, mientras que {\tt labelLVPair} extrae
la etiqueta de un par etiqueta-valor. Como implementamos las familias de tipos
como tipos indizados en clases la misma informaci\'on se ve replicada en el
nivel de los tipos, por lo que son necesarias restricciones como
{\tt HMember t nts}, {\tt Defs att nts vs ic} o
{\tt SingleDef mch mnts att (Tagged (lch,t) vch) ic')}.
Las restricciones que se refieren a tipos indizados como:

> ic'  ~ DefsR att nts vs ic
> mnts ~ HMemberRes t nts
> mch  ~ HasLabelChildAttsRes (lch,t) ic'

no son estrictamente necesarias, y podr\'ian en todos los casos eliminarse
y utilizar el lado derecho en cada ocurrencia del lado izquierdo.\footnote{
  a modo de ejemplo, cuando se define
  {\tt SingleDefR}, en su segundo par\'ametro n\'otese que
  escribimos {\tt HMemberRes t nts}, en lugar de {\tt mnts}.
}

La funci\'on 
{\tt singledef} implementa la inserci\'on en la atribuci\'on de un hijo.
La definici\'on de la clase utilizada para la funci\'on viene dada por:

> class SingleDef (mch::Bool)(mnts::Bool) att pv (ic ::[(k',[(k,Type)])]) where
>   type SingleDefR mch mnts att pv ic :: [(k',[(k,Type)])]
>   singledef :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
>                 -> ChAttsRec (SingleDefR mch mnts att pv ic)


Los primeros dos par\'ametros son, como vimos antes proxies de booleanos,
que proveen evidencia de la existencia de las etiquetas del hijo y los
terminales respectivamente.
El caso v\'alido, en donde el c\'odigo debe compilar es cuando ambos
valen {\tt True}. Las dem\'as combinaciones sirven para definir mensajes de
error expresivos en cada escenario, utilizando {\tt GHC.TypeLits.TypeError}.
La implementaci\'on del caso interesante es la siguiente:

> instance ( HasChildF lch ic
>          , och ~ LookupByChildFR lch ic
>          , UpdateAtChildF lch ( '(att,vch) ': och) ic
>          , LabelSet ( '(att, vch) ': och)) =>
>   SingleDef 'True 'True att (Tagged lch vch) ic where
>   type SingleDefR 'True 'True att (Tagged lch vch) ic
>     = UpdateAtChildFR lch ( '(att,vch) ': (LookupByChildFR lch ic)) ic
>   singledef _ _ att pch ic
>     = updateAtChildF (Label :: Label lch) ( att =. vch *. och) ic
>     where lch = labelTChAtt pch
>           vch = unTaggedChAtt pch
>           och = lookupByChildF lch ic

Se obtiene la atribuci\'on del hijo de nombre adecuado ({\tt och})
y se inserta el atributo en la misma, lo que corresponde a la expresi\'on
{\tt att =.vch *.och}. El operador
{\tt (*.)} es azucar sint\'actica para {\tt ConsAtt}\footnote{
  En general {\tt (*.)}, {\tt (=.)}, {\tt (\#.)} corresponden a atribuciones,
  mientras que {\tt (.*)}, {\tt (.=)}, {\tt (.\#)} corresponden a mapeos
  de hijos. Existen versiones sobrecargadas de los operadores como vimos
  anteriormente en la secci\'on~\ref{labels} con el uso de {\tt (\#)}.
  En ciertos escenarios el uso de la sobrecarga puede llevar a requerir
  anotar tipos y conducir a errores de compilaci\'on confusos. Es recomendable
  para los nuevos usuarios de la biblioteca, utilizar los constructores
  especializados.
}, por lo que
est\'aticamente se requiere satisfacer la restricci\'on
{\tt LabelSet ('(att, vch) ':och))}. Finalmente la nueva atribuci\'on 
es insertada en el registro de atribuciones de los hijos usando
{\tt updateAtChildF}.

En todas las definiciones anteriores las funciones auxiliares utilizadas en las
cl\'ausulas {\tt where} son funciones de acceso o predicados relativamente
simples de definir. Como vimos, algunos de los valores que se retornan contienen
informaci\'on a nivel de tipos usada en tiempo de compilaci\'on.
{\tt lch}, {\tt mch}, {\tt mnts} son ejemplos de expresiones que
no tienen informaci\'on a nivel de valores.

Por ejemplo {\tt hasLabelChildAtts} predica
la existencia de una etiqueta de hijo a nivel de tipos. Se define como
familia de tipos y todo el contenido computacional se da a nivel de los tipos,
a nivel de valores se retorna un Proxy.

> class HasLabelChildAtts (e :: k)(r :: [(k,[(k,Type)])]) where
>   type HasLabelChildAttsRes (e::k)(r :: [(k,[(k,Type)])]) :: Bool
>   hasLabelChildAtts
>    :: Label e -> ChAttsRec r -> Proxy (HasLabelChildAttsRes e r)

La implementaci\'on es inmediata, buscamos la ocurrencia de la etiqueta
en las primeras componentes de una lista de pares:

> instance HasLabelChildAtts e '[] where
>   type HasLabelChildAttsRes e '[] = 'False
>   hasLabelChildAtts _ _ = Proxy

> instance HasLabelChildAtts k ( '(k' ,v) ': ls) where
>   type HasLabelChildAttsRes k ( '(k' ,v) ': ls)
>       = Or (k == k') (HasLabelChildAttsRes k ls)
>   hasLabelChildAtts _ _ = Proxy


Por otra parte, {\tt Or} es una funci\'on definida puramente a nivel de tipos,
y la implementamos como familia.

> type family Or (l :: Bool)(r :: Bool) :: Bool where
>   Or False b = b
>   Or True b  = 'True




Como ejemplo de una primitiva no usada en {\tt repmin}
podemos citar {\tt synmod},
que redefine un atributo sintetizado existente (tanto el valor, como el tipo).

> synmod  ::  UpdateAtLabelAtt att val sp sp' =>
>     Label att -> val -> Fam ic sp -> Fam ic sp'
> synmod latt val (Fam ic sp) = Fam ic (updateAtLabelAtt latt val sp)


\subsection{Aspectos}

Un aspecto se implementa
simplemente como un registro heterogeneo que contendr\'a reglas
etiquetadas por nombres de producciones.

> type Aspect = Record
> type Prd prd rule = Tagged prd rule

En este caso no consideramos
necesaria una implementaci\'on especializada y preferimos
reutilizar c\'odigo, en contraste a la implementaci\'on de las
atribuciones y registros de atribuciones de los hijos,
en donde la estructura es compleja e induce a errores de programaci\'on
(por lo que prefer\'iamos tipar lo m\'as fuertemente posible).
De cualquier manera, para el usuario de la biblioteca la
construcci\'on de malas instancias puede ser prohibida por constructores
inteligentes. En particular al utilizar el combinador de aspectos
se utiliza la funci\'on {\tt comSingle} que solo compila si las reglas
est\'an bien formadas, como vemos m\'as adelante.

\subsection{Combinaci\'on de Aspectos}

La combinaci\'on de aspectos viene dada por la funci\'on {\tt (.+.)}
definida a nivel de tipos como la clase {\tt Com}.

> class Com (r :: [(k,Type)]) (s :: [(k, Type)]) where
>   type (.++.) r s :: [(k,Type)]
>   (.+.) :: Aspect r -> Aspect s -> Aspect (r .++. s)

La funci\'on se define por recursi\'on en la segunda componente.
Si una producci\'on aparece en un solo aspecto par\'ametro aparecer\'a
en el resultado intacta. Por otro lado, las
producciones que aparezcan en ambos aspectos deber\'an incluirse
en el resultado
con las reglas combinadas seg\'un la funci\'on {\tt ext} definida
anteriormente.

Para el caso base, donde el segundo aspecto es vac\'io
la funci\'on retorna el primer aspecto sin modificar.

> instance Com r '[] where
>   type r .++. '[] = r
>   r .+. _ = r

Si la segunda componente consiste en al menos una producci\'on con su regla,
la combinamos al primer aspecto mediante la funci\'on {\tt comSingle},
y llamamos recursivamente a la combinaci\'on del nuevo registro creado con la
cola del segundo par\'ametro.

> instance ( Com (ComSingleR (HasLabelRecRes prd r) prd rule r)  r'
>          , HasLabelRecRes prd r ~ b
>          , HasLabelRec prd r
>          , ComSingle b prd rule r)
>   => Com r ( '(prd, rule) ': r') where
>      type r .++. ( '(prd, rule) ': r')
>        = (ComSingleR (HasLabelRecRes prd r) prd rule r) .++. r'
>      r .+. (pr `ConsR` r') = let b   = hasLabelRec (labelPrd pr) r
>                                  r'''= comSingle b pr r
>                                  r'' = r''' .+. r'
>                              in  r''


La funci\'on {\tt comSingle} es una funci\'on cuyo comportamiento
es dependiente de los tipos de la producci\'on y el Aspecto par\'ametro.
Si ya existe una producci\'on con ese nombre se deben combinar las reglas
en el campo correspondiente del aspecto, sino el Aspecto debe extenderse.
Implementamos {\tt ComSingle} con un par\'ametro booleano extra que indica
la pertenencia o no de la etiqueta {\tt prd} al registro {\tt r}.
La firma viene dada por:

> class ComSingle (b::Bool) (prd :: k) (rule :: Type) (r :: [(k,Type)]) where
>   type ComSingleR b prd rule r :: [(k, Type)]
>   comSingle :: Proxy b -> Prd prd rule -> Aspect r
>             -> Aspect (ComSingleR b prd rule r)


Nuevamente hacemos uso del proxy para propagar pruebas.
La funci\'on {\tt hasLabelRec}
se define an\'alogamente a {\tt hasLabelChildAtts}.
Luego podemos definir las instancias posibles de {\tt ComSingle}, y adem\'as
chequeamos ciertas propiedades de buena formaci\'on.
En particular cuando combinamos reglas
chequeamos que efectivamente estamos combinando reglas.


En el caso donde la etiqueta de la producci\'on a insertar no est\'a presente
en el aspecto par\'ametro simplemente extendemos el aspecto:

> instance ( LabelSet ('(prd, rule) ': r)) => 
>   ComSingle 'False prd rule r where
>   type ComSingleR 'False prd rule r = '(prd, rule) ': r
>   comSingle _ prd asp = prd .*. asp


Si la producci\'on ya exist\'ia en el aspecto par\'ametro, obtenemos
la regla correspondiente, la combinamos con la nueva ({\tt ext}),
e insertamos la regla resultante
en el aspecto.

> instance ( UpdateAtLabelRecF prd (Rule sc ip ic  sp  ic'' sp'') r
>          , HasFieldRec prd r
>          , LookupByLabelRec prd r ~ (Rule sc ip ic' sp' ic'' sp'')
>          , ic'' ~ (Syn3 (LookupByLabelRec prd r))
>          , sp'' ~ (Inh3 (LookupByLabelRec prd r))
>          ) =>
>   ComSingle 'True prd (Rule sc ip ic  sp  ic'  sp') r where
>   type ComSingleR 'True prd (Rule sc ip ic  sp  ic'  sp') r
>     = UpdateAtLabelRecFR prd (Rule sc ip ic sp ic'' sp'') r
>   comSingle _ f r = updateAtLabelRecF l (oldR `ext` newR) r 
>     where l    = labelPrd f
>           oldR = lookupByLabelRec l r
>           newR = rulePrd f


Donde {\tt Syn3} e {\tt Inh3} son funciones de proyecci\'on definidas
puramente a nivel de tipos:

> type family Syn3 (rule :: Type) :: [(k', [(k, Type)])] where
>   Syn3 (Rule sc ip ic  sp  ic'' sp'') = sp''
> type family Inh3 (rule :: Type) :: [(k, Type)] where
>   Inh3 (Rule sc ip ic  sp  ic'' sp'') = ic''



\subsection{Funciones sem\'anticas}

En cada producci\'on, llamamos ``funci\'on sem\'antica'' al mapeo de los
atributos heredados a los atributos sintetizados. Una
computaci\'on sobre la gram\'atica
consiste exactamente en computar las funciones sem\'anticas.

En el ejemplo {\tt repmin}, la funci\'on {\tt sem\_Tree} construye,
dados un aspecto y un \'arbol, una funci\'on sem\'antica.
El tipo de {\tt sem\_Tree}, si ignoramos los par\'ametros impl\'icitos
de las restricciones de typeclasses, viene dado por:

> sem_Tree :: Aspect r -> Tree -> Attribution ip -> Attribution sp

Observemos la definici\'on en uno de los casos:

> sem_Tree asp (Node l r) =  knit (asp .#. p_Node) $
>                            ch_l .=. sem_Tree asp l
>                        .*. ch_r .=. sem_Tree asp r
>                        .*. emptyRecord

Es la funci\'on {\tt knit} la que se encarga de construir la funci\'on
sem\'antica a partir de las funciones sem\'anticas de los hijos.

El tipo completo de {\tt sem\_Tree} es:
\newpage

> sem_Tree
>   :: (HasFieldRec P_Node r, HasFieldRec P_Leaf r,
>       LookupByLabelRec P_Node r
>       ~ (Rule '[ '((Ch_l, Tree),  sp), '((Ch_r, Tree),  sp)]  ip
>               '[ '((Ch_l, Tree), '[]), '((Ch_r, Tree), '[])] '[]
>               '[ '((Ch_l, Tree),  ip), '((Ch_r, Tree),  ip)]  sp),
>       LookupByLabelRec P_Leaf r
>       ~ (Rule  '[ '((Ch_i, Int), '[ '((Val, Int), Int)])]     ip
>                '[ '((Ch_i, Int), '[])]                       '[]
>                '[ '((Ch_i, Int),  p)]                         sp)) =>
>      Aspect r -> Tree -> Attribution ip -> Attribution sp

Se aprecian m\'ultiples predicados que deben chequearse para que las llamadas
a {\tt sem\_Tree} {\bf compilen}. Una llamada donde el aspecto {\tt r} no
contenga definiciones para los nodos o para las hojas no compilar\'a
(observar las restricciones, por ejemplo que {\tt LookupByLabelRec P\_Node r}
debe ser equivalente a una regla que contenga computaciones para
los hijos {\tt Ch\_l} y {\tt Ch\_r}).
 Por supuesto, como un aspecto
es un registro no van a permitirse instancias donde se dupliquen etiquetas
de producciones. No existe sin embargo ninguna restricci\'on sobre el largo
de {\tt r} o las etiquetas adicionales que contiene, lo cual tiene sentido
porque eventualmente la gram\'atica podr\'ia extenderse con nuevas
producciones.


\subsection{La funci\'on {\tt knit}}

La funci\'on {\tt knit}~\cite{DBLP:conf/gcse/MoorPW99}
realiza la verdadera computaci\'on. Toma
las reglas combinadas para una producci\'on y las funciones sem\'anticas
de los hijos, y construye la funci\'on sem\'antica del padre.

> knit :: ( Empties fc , EmptiesR fc ~ ec
>         , Kn fc ic sc )
>   => Rule sc ip ec '[] ic sp -> Record fc -> Attribution ip -> Attribution sp
> knit rule fc ip
>   = let ec          = empties fc
>         (Fam ic sp) = rule (Fam sc ip) (Fam ec EmptyAtt)
>         sc          = kn fc ic
>     in  sp

Primero se construye una familia de salida vac\'ia, mediante la funci\'on
{\tt empties}. Esta contiene atribuciones vac\'ias tanto para el padre como
para todos los hijos. A partir de la familia de entrada y nuestra familia
``dummy'' construimos la familia de salida. La familia de entrada consta
de los atributos heredados del padre {\tt ip} que tenemos disponibles como
par\'ametro, y de los sintetizados de los hijos {\tt sc}. Tenemos disponibles
los atributos heredados de los hijos y las funciones sem\'anticas, por lo que
para computar {\tt sc} debemos ejecutar {\tt knit} en cada uno de los hijos,
trabajo realizado por la funci\'on {\tt kn}.

La funci\'on {\tt empties} se define por recursi\'on,
sin mayores complicaciones:

> class Empties (fc :: [(k,Type)]) where
>   type EmptiesR fc :: [(k, [(k, Type)])]
>   empties :: Record fc -> ChAttsRec (EmptiesR fc)


> instance Empties '[] where
>   type EmptiesR '[] = '[]
>   empties EmptyR = EmptyCh


> instance (Empties fcr,
>           LabelSet ( '(lch, '[]) ': EmptiesR fcr)) =>
>   Empties ( '(lch, fch) ': fcr) where
>   type EmptiesR ( '(lch, fch) ': fcr) = '(lch, '[]) ': EmptiesR fcr
>   empties (ConsR pch fcr)
>     = let lch = labelTChAtt pch
>       in  ConsCh (TaggedChAttr lch EmptyAtt) (empties fcr)


La funci\'on {\tt kn} es una porci\'on de c\'odigo bastante t\'ecnica de
programaci\'on a nivel de tipos.
Dadas las funciones sem\'anticas de los hijos y sus entradas
(atributos heredados de los hijos) se construyen los atributos sintetizados
para los hijos. La funci\'on deber\'ia tener un tipo similar a:

> kn :: Record fcr -> ChAttsRec ich -> ChAttsRec sch

Pero observemos que {\tt ich} y {\tt sch} est\'an determinados por el contenido
de las funciones sem\'anticas.
La clase entonces se implementa con la firma:

> class Kn (fcr :: [(k, Type)]) where
>   type ICh fcr :: [(k, [(k, Type)])]
>   type SCh fcr :: [(k, [(k, Type)])]
>   kn :: Record fcr -> ChAttsRec (ICh fcr) -> ChAttsRec (SCh fcr)

Y luego la funci\'on {\tt kn} se implementa por recursi\'on en la forma de la
funci\'on sem\'antica. En alg\'un sentido esta funci\'on se asemeja a
 {\tt zipWith \$}:

> instance Kn '[] where
>   type ICh '[] = '[]
>   type SCh '[] = '[] 
>   kn _ _ = EmptyCh

> instance ( Kn fc
>          , LabelSet ('(lch, sch) : SCh fc)
>          , LabelSet ('(lch, ich) : ICh fc)) => 
>   Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) where
>   type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , ich) ': ICh fc
>   type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , sch) ': SCh fc
>   kn (ConsR pfch fcr) (ConsCh pich icr)
>    = let scr = kn fcr icr
>          lch = labelTChAtt pfch
>          fch = unTagged pfch
>          ich = unTaggedChAttr pich
>      in ConsCh (TaggedChAttr lch (fch ich)) scr
