\subsection{Estructuras de Datos}

Como se defini\'o antes,
una atribuci\'on (\emph{attribution}) es un mapeo de nombres de atributos
(que ser\'an represenentados puramente a nivel de tipos como etiquetas)
a sus valores. La estructura de Registro extensible (fuertemente tipado)
presentada anteriormente es ideal para representarles.

Para obtener mensajes de error precisos y evitar que se filtre
implementaci\'on en los mismos, decidimos tener estructuras especializadas.

Un atributo (etiquetado) viene entonces dado por:

> newtype Attribute label value = Attribute value

que es el componente principal para construir atribuciones:

> data Attribution :: forall k . [(k,Type)] -> Type where
>   EmptyAtt :: Attribution '[]
>   ConsAtt  :: LabelSet ( '(att, val) ': atts) =>
>    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)

Notar que ya estamos utilizando todo el poder de las extensiones modernas.
Se utilizan kinds promovidos en las listas ({\tt -XDataKinds}),
polimorfismo en kinds en las etiquetas ({\tt -XPolyKinds})
la estructura es un GADT ({\tt -XGADTs}), LabelSet est\'a predicando sobre
un kind
polim\'orfico (por lo que usamos kind equality)({\tt ConstraintKinds}),
y el kind {\tt Type} fu\'e introducido en {\tt -XTypeInType}.

Una {\tt familia} consiste en la atribuci\'on del padre y una colecci\'on
de atribuciones para los hijos (etiquetadas por sus nombres).

Representamos \'esta \'ultima estructura como

> data ChAttsRec :: forall k k' . [(k , [(k',Type)])] -> Type where
>   EmptyCh :: ChAttsRec '[]
>   ConsCh  :: LabelSet ( '(l, v) ': xs) =>
>    TaggedChAttr l v -> ChAttsRec xs -> ChAttsRec ( '(l,v) ': xs)

Notar la analog\'ia con la anterior, es de nuevo una implementaci\'on de
Registro heterogeneo, especializada.
Notar tambi\'en que las etiquetas no tienen por qu\'e tener el mismo kind.
Esto se decidi\'o as\'i para soportar posiblemente a futuro
la generaci\'on de etiquetas por parte
del programador a nivel de valores y usar los kinds promovidospara las mismas.

Dado que una atribuci\'on una vez bajo
el wrapper {\tt Attrribution} tiene kind {\tt Type}, podr\'iamos haber
implementado a los hijos como un registro agn\'ostico respecto al contenido.
Se prefiere una implementaci\'on fuertemente tipada sobre reutilizar
el c\'odigo existente.

En cada nodo de la gram\'atica, una \emph{Familia} contiene la atribuci\'on
del padre y la colecci\'on de atribuciones de los hijos.

> data Fam (c::[(k,[(k,Type)])]) (p :: [(k,Type)]) :: Type where
>   Fam :: ChAttsRec c  -> Attribution p -> Fam c p

Una regla es una funci\'on de la familia de entrada a la de salida,
el tipo de las reglas se implementa con una aridad extra para hacerlas
componibles, como en [REF al paper de Moor et al]

> type Rule sc ip ic sp ic' sp'
>   = Fam sc ip -> (Fam ic sp -> Fam ic' sp')
> (f `ext` g) input = f input . g input


Para ser m\'as precisos, el tipo de rule:

> type Rule (sc  :: [(k', [(k, Type)])])
>           (ip  :: [(k,       Type)])
>           (ic  :: [(k', [(k, Type)])])
>           (sp  :: [(k,       Type)])
>           (ic' :: [(k', [(k, Type)])])
>           (sp' :: [(k,       Type)])
>   = Fam sc ip -> Fam ic sp -> Fam ic' sp'



\subsection{Declaraciones de Reglas}

Se proveen distintas construcciones para luego declarar reglas.
En el ejemplo se utilizaron {\tt syndef} e {\tt inhdef}, que son
las m\'inimas adecuadas para tener un sistema interesante.

En la implementaci\'on se proveen otras construcciones, y parte
del trabajo futuro pasa por codificar otras nuevas.

Por ejemplo, la funci\'on {\tt syndef} provee la definici\'on de un nuevo
atributo sintetizado.
Dada una etiqueta no definida previamente, que represente el
nombre del atributo a definir, y un valor para el mismo,
construye una funci\'on que actualiza la familia construida hasta el momento.

> syndef  :: LabelSet ( '(att,val) ': sp) =>
>     Label att -> val -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
> syndef latt val (Fam ic sp) = Fam ic (latt =. val *. sp)


Como ejemplo de una primitiva alternativa,

> synmod  ::  UpdateAtLabelAtt att val sp sp'
>   =>  Label att -> val -> Fam ic sp -> Fam ic sp'
> synmod att v (Fam ic sp) = Fam ic (updateAtLabelAtt att v sp)


La funci\'on {\tt inhdef} introduce un atributo heredado
de nombre {\tt att} para una colecci\'on de no terminales {\tt nts}.
{\tt vals} es un registro con claves consistentes en los nombres de
los hijos, conteniendo valores que describen como computar el atributo
que est\'a siendo definido para cada uno de ellos.
En contraste con {\tt syndef}, es bastante m\'as compleja de implementar. 

Primero, es necesaria una funci\'on auxiliar insertar una definici\'on en
la atribuci\'on de un hijo:

> class SingleDef (mch::Bool)(mnts::Bool) att pv (ic ::[(k,[(k,Type)])])
>                  (ic' ::[(k,[(k,Type)])]) | mch mnts att pv ic -> ic' where
>   singledef :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
>                -> ChAttsRec ic'



> instance ( HasChild lch ic och
>          , UpdateAtChild lch ( '(att,vch) ': och) ic ic'
>          , LabelSet ( '(att, vch) ': och))
>   => SingleDef True True att (Tagged lch vch) ic ic' where
>   singledef _ _ att pch ic =
>     updateAtChild (Label :: Label lch) ( att =. vch *. och) ic
>     where lch = labelTChAtt pch
>           vch = unTaggedChAtt pch
>           och = lookupByChild lch ic

[MOSTRAR MAS COSAS]






\subsection{Aspectos}
\subsubsection{Definifi\'on}

Un aspecto (\emph{aspect}) se implementa
simplemente como un registro heterogeneo, (que contendr\'a reglas,
etiquetadas por nombres de producciones).
En este caso no consideramos
necesaria une implementaci\'on especializada. En contraste a las
atribuciones y registros de atribuciones de los hijos,
en donde la estructura es compleja e induce a errores de programaci\'on
(por lo que preferimos tipar lo m\'as fuertemente posible),
aqu\'i se prefiere reutilizar c\'odigo.

Notar que de cualquier manera, para el usuario de la biblioteca la
construcci\'on de malas instancias puede ser prohibida por constructores
inteligentes. En particular al utilizar el combinador de aspectos
se utiliza la funci\'on {\tt comSingle} que solo compila si las reglas
est\'an bien formadas, como vemos m\'as adelante.

Tenemos disponible el poder de los
tipos dependientes (casi, al menos una simulaci\'on de los mismos) y
podr\'iamos chequear otras propiedades.

> type Aspect = Record                 -- tipo de los Aspectos
> type Prd prd rule = Tagged prd rule  -- tipo de las producciones


\subsubsection{Combinaci\'on de Aspectos}

La combinaci\'on de aspectos viene dada por la funci\'on {\tt .+.}
definida a nivel de tipos como la clase {\tt Com}.

> class Com (r :: [(k,Type)]) (r' :: [(k, Type)]) (r'' :: [(k,Type)])
>   | r r' -> r'' where
>   (.+.) :: Aspect r ->  Aspect r' ->  Aspect r''

La funci\'on inserta en el resultado intactas las producciones que aparecen
en un solo aspecto par\'ametro. Por otro lado las
producciones que aparezcan en ambos aspectos deber\'an incluirse
con las reglas combinadas (seg\'un la funci\'on {\tt ext} definida
previamente).

La funci\'on de combinaci\'on viene definida por recursi\'on en la
segunda componente. Si el segundo registro es vac\'io,
en la operaci\'on es neutro.

> instance Com r '[] r where
>   r .+. _ = r


Si la segunda componente consiste en al menos una producci\'on con su regla,
la combinamos al primer aspecto mediante la funci\'on {\tt comSingle},
y llamamos recursivamente a la combinaci\'on del nuevo registro creado con la
cola del segundo par\'ametro.

> instance ( Com r''' r' r''
>          , HasLabelRec prd r
>          , ComSingle (HasLabelRecRes prd r) prd rule r r''')
>   => Com r ( '(prd, rule) ': r') r'' where
>      r .+. (pr `ConsR` r') = let 
>                                  b   = hasLabelRec (labelPrd pr) r
>                                  r'''= comSingle b pr r
>                                  r'' = r''' .+. r'
>                              in  r''

La funci\'on {\tt comSingle} es una funci\'on cuyo comportamiento
es dependiente de los tipos de la producci\'on y el Aspecto par\'ametro.
Si ya existe una producci\'on con ese nombre de deben combinar las reglas
en el campo correspondiente del aspecto, sino, el Aspecto debe extenderse.
Implementamos {\tt ComSingle} con un par\'ametro booleano extra que indica
la pertenencia o no de la etiqueta {\tt prd} al registro {\tt r}
La firma viene dada por:

> class ComSingle (b::Bool) (prd :: k) (rule :: Type) (r₁ :: [(k,Type)])
>                 (r₂ :: [(k,Type)]) | b prd rule r₁ -> r₂ where
>   comSingle :: Proxy b -> Prd prd rule -> Aspect r₁ -> Aspect r₂

Como se detall\'o en la secci\'on \ref{sec:sings}, en Haskell
requerimos testigos en tiempo de ejecuci\'on en computaciones de tipos
dependientes, por lo que debemos incluir el par\'ametro {\tt Proxy b}.

Como se aprecia en la definici\'on del caso recursivo de la clase
{\tt Com}, el booleano, tanto a nivel de tipos como de valores es una
funci\'on predicado de pertenencia para los registros
({HasLabelRec}/{\tt hasLabelRec}).

> class HasLabelRec (e :: k)(r ::[(k,Type)]) where
>   type HasLabelRecRes (e::k)(r ::[(k,Type)]) :: Bool
>   hasLabelRec :: Label e -> Record r -> Proxy (HasLabelRecRes e r)

> instance HasLabelRec e '[] where
>   type HasLabelRecRes e '[] = 'False
>   hasLabelRec _ _ = Proxy

> instance HasLabelRec  k ( '(k' ,v) ': ls) where
>   type HasLabelRecRes k ( '(k' ,v) ': ls)
>       = Or (k == k') (HasLabelRecRes k ls)
>   hasLabelRec _ _ = Proxy

en este caso usamos un tipo indizado en lugar de dependencias funcionales.
\textcolor{blue}{[esto no es muy justificable,
en realidad habr\'ia que converger a las type
families, y despu\'es lo har\'e pero mientras est\'an estos baches que no se
bien como justificar]}

{\tt Or} es una funci\'on definida
puramente a nivel de tipos, y la implementamos como
una \emph{Type Family}

> type family Or (l :: Bool)(r :: Bool) :: Bool where
>   Or False b = b
>   Or True b  = 'True


Luego podemos definir las instancias posibles de {\tt ComSingle}, y adem\'as
chequeamos ciertas propiedades. En particular cuando combinamos reglas
chequeamos que efectivamente estamos combinando reglas.


> instance (LabelSet ('(prd, rule) : r₁))
>    => ComSingle 'False prd rule r₁ ( '(prd,rule) ': r₁) where
>   comSingle _ prd asp = prd `ConsR` asp

> instance ( HasFieldRec prd r,
>            LookupByLabelRec prd r ~ (Rule sc ip ic' sp' ic'' sp'')
>          , UpdateAtLabelRec prd (Rule sc ip ic  sp  ic'' sp'') r r'
>          )
>   => ComSingle 'True prd        (Rule sc ip ic  sp  ic'  sp') r r' where
>   comSingle _ f r = updateAtLabelRec l (oldR `ext` newR) r :: Aspect r' 
>     where l    = labelPrd f                                :: Label prd
>           oldR = lookupByLabelRec l r    
>           newR = rulePrd f


\subsubsection{Funciones sem\'anticas}

En cada producci\'on, llamamos \emph{funci\'on sem\'antica} al mapeo de los
atributos heredados a los atributos sintetizados. Obs\'ervese que una
computaci\'on consiste en exactamente computar las funciones sem\'anticas.

En el ejemplo [REF], la funci\'on {\tt sem\_Tree} construye,
dados un aspecto y un \'arbol una funci\'on sem\'antica.
El tipo de {\tt sem\_Tree}, si ignoramos los par\'ametros impl\'icitos
de las restricciones de typeclasses, viene dado por:

> sem_Tree :: Aspect r -> Tree -> Attribution ip -> Attribution sp

Observemos la definici\'on en uno de los casos:

> sem_Tree asp (Node l r) =  knit (asp .#. p_Node) $
>                            ch_l .=. sem_Tree asp l
>                        .*. ch_r .=. sem_Tree asp r
>                        .*. emptyRecord

Es la funci\'on {\tt knit} la que se encarga de construir la funci\'on
sem\'antica a partir de las funciones sem\'anticas de los hijos (notar que
cada llamada recursiva a {\tt sem\_Tree}, parcialmente aplicada a dos
par\'ametros es exactamente una funci\'on sem\'antica).

El tipo completo de {\tt sem\_Tree} viene dado por:

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
a {\tt sem\_Tree} {\bf compilen}. Una llamada donde el Aspecto {\tt r} no
contenga definiciones para los nodos o para las hojas no compilar\'a.
Adem\'as en el valor imagen de cada una de \'estas etiquetas debe haber una
regla que cumpla ciertas restricciones de forma. Por supuesto, como un aspecto
es un registro, por lo que
no van a permitirse instancias donde se dupliquen etiquetas
de producciones. No existe sin embargo ninguna restricci\'on sobre el largo
de {\tt r} o las etiquetas adicionales que contiene, lo cual tiene sentido
porque eventualmente la gram\'atica podr\'ia extenderse con nuevas producciones.


\subsubsection{La funci\'on {\tt knit}}

La funci\'on {\tt knit}[REF] realiza la verdadera computaci\'on. Toma
las reglas combinadas para una producci\'on, y las funciones sem\'anticas
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
{\tt empties}. \'Esta contiene atribuciones vac\'ias tanto para el padre como
para todos los hijos. A partir de la familia de entrada y nuestra familia
``dummy'' construimos la familia de salida. La familia de entrada consta
de los atributos heredados del padre {\tt ip} que tenemos disponibles como
par\'ametro, y de los sintetizados de los hijos {\tt sc}. Tenemos disponibles
los atributos heredados de los hijos y las funciones sem\'anticas, por lo que
para computar {\tt sc} debemos ejecutar {\tt knit} en cada uno de los hijos,
trabajo realizado por la funci\'on {\tt kn}, que es una funci\'on {\tt map}
especializada.


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
>     = let lch = labelTChAtt pch -- TODO: name
>       in  ConsCh (TaggedChAttr lch EmptyAtt) (empties fcr)

> class Kn (fcr :: [(k, Type)])
>          (icr :: [(k, [(k, Type)])])
>          (scr :: [(k, [(k, Type)])]) | fcr -> scr icr where 
>   kn :: Record fcr -> ChAttsRec icr -> ChAttsRec scr

> instance Kn '[] '[] '[]
>   kn _ _ = EmptyCh


> instance ( Kn fc ic sc
>          , LabelSet ('(lch, sch) : sc)
>          , LabelSet ('(lch, ich) : ic))
>   =>  Kn ( '(lch , Attribution ich -> Attribution sch) ': fc)
>          ( '(lch , ich) ': ic)
>          ( '(lch , sch) ': sc) where
>   kn (ConsR pfch fcr) (ConsCh pich icr)
>    = let scr = kn fcr icr
>          lch = labelTChAtt pfch    :: Label lch
>          fch = unTagged pfch       :: Attribution ich -> Attribution sch
>          ich = unTaggedChAttr pich :: Attribution ich
>      in ConsCh (TaggedChAttr lch (fch ich)) scr


