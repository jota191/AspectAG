\subsection{Estructuras de Datos}

Como se defini\'o antes,
una atribuci\'on (\emph{attribution}) es un mapeo de nombres de atributos
a sus valores, que representamos como un registro heterogeneo.
Para obtener mensajes de error precisos y evitar que se filtre
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
polimorfismo en kinds en las etiquetas ({\tt PolyKinds})
la estructura es un GADT ({\tt GADTs}), LabelSet est\'a predicando sobre
un kind
polim\'orfico, donde usamos igualdad de kinds, ({\tt ConstraintKinds}).

Una \emph{familia} consiste en la atribuci\'on del padre y una colecci\'on
de atribuciones para los hijos (etiquetadas por sus nombres).

Representamos \'esta \'ultima estructura como

> data ChAttsRec :: forall k k' . [(k , [(k',Type)])] -> Type where
>   EmptyCh :: ChAttsRec '[]
>   ConsCh  :: LabelSet ( '(l, v) ': xs) =>
>    TaggedChAttr l v -> ChAttsRec xs -> ChAttsRec ( '(l,v) ': xs)

La estructura es an\'aloga a la anterior: es de nuevo una implementaci\'on de
registro heterogeneo especializada.

Estamos en condiciones de definir las familias:

> data Fam (c::[(k,[(k,Type)])]) (p :: [(k,Type)]) :: Type where
>   Fam :: ChAttsRec c  -> Attribution p -> Fam c p

Una regla es una funci\'on de la familia de entrada a la de salida,
el tipo de las reglas se implementa con una aridad extra para hacerlas
componibles~\cite{Moor99first-classattribute}.
\label{rule}

> type Rule sc ip ic sp ic' sp'
>   = Fam sc ip -> (Fam ic sp -> Fam ic' sp')
> (f `ext` g) input = f input . g input


Para ser m\'as precisos, podr\'ia declararse como:

> type Rule (sc  :: [(k', [(k, Type)])])
>           (ip  :: [(k,       Type)])
>           (ic  :: [(k', [(k, Type)])])
>           (sp  :: [(k,       Type)])
>           (ic' :: [(k', [(k, Type)])])
>           (sp' :: [(k,       Type)])
>   = Fam sc ip -> Fam ic sp -> Fam ic' sp'



\subsection{Declaraciones de Reglas}

Se proveen distintas primitivas para declarar reglas.
En el ejemplo se utilizaron {\tt syndef} e {\tt inhdef}, que son
las m\'inimas adecuadas para tener un sistema utilizable.
En la implementaci\'on se proveen otras construcciones, y parte
del trabajo futuro pasa por codificar nuevas.

La primitiva {\tt syndef} provee la definici\'on de un nuevo
atributo sintetizado.
Dada una etiqueta no definida previamente que represente el
nombre del atributo a definir, y un valor para el mismo,
construye una funci\'on que actualiza la familia construida hasta el momento.

> syndef  :: LabelSet ( '(att,val) ': sp) =>
>     Label att -> val -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
> syndef latt val (Fam ic sp) = Fam ic (latt =. val *. sp)

Los operadores {\tt (=.)} y {\tt (*.)} son azucar sint\'actica para
El constructor de atributos {\tt Attribute} y para {\tt ConsAtt},
respectivamente.

Como ejemplo de una primitiva no usada en {\tt repmin}
podemos citar {\tt synmod},
que redefine un atributo sintetizado existente.


> synmod  ::  UpdateAtLabelAtt att val sp sp'
>   =>  Label att -> val -> Fam ic sp -> Fam ic sp'
> synmod latt val (Fam ic sp) = Fam ic (updateAtLabelAtt latt val sp)

Por otro lado,
la funci\'on {\tt inhdef} introduce un atributo heredado
de nombre {\tt att} para una colecci\'on de no terminales {\tt nts}.

> inhdef :: Defs att nts vals ic ic'
>   => Label att -> HList nts -> Record vals -> (Fam ic sp -> Fam ic' sp)
> inhdef att nts vals (Fam ic sp) = Fam (defs att nts vals ic) sp


{\tt vals} es un registro con claves consistentes en los nombres de
los hijos, conteniendo valores que describen como computar el atributo
que est\'a siendo definido para cada uno de ellos.
En contraste con {\tt syndef}, es bastante m\'as compleja de implementar,
y para ello utilizmos la funci\'on auxiliar {\tt defs}, que inserta las
definiciones en los hijos a los que corresponda.

Primero, es necesario proveer la inserci\'on en
la atribuci\'on de un hijo:

> class SingleDef (mch::Bool)(mnts::Bool) att pv (ic ::[(k',[(k,Type)])]) where
>   type SingleDefR mch mnts att pv ic :: [(k',[(k,Type)])]
>   singledef :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
>                 -> ChAttsRec (SingleDefR mch mnts att pv ic)

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


Los par\'ametros {\tt mch} y {\tt mnts} son Proxys de booleanos,
que proveen evidencia de la existencia de las etiquetas del hijo o los
terminales.
Finalmente estamos en condiciones de definir la funci\'on {\tt defs}.
Se hace recursi\'on sobre
el registro {\tt vals} que contiene las nuevas definiciones. Utilizanando
{\tt singledef} se insertan las definiciones.

> class Defs att (nts :: [Type])
>             (vals :: [(k,Type)]) (ic :: [(k',[(k,Type)])]) where
>   type DefsR att nts vals ic :: [(k',[(k,Type)])]
>   defs :: Label att -> HList nts -> Record vals -> ChAttsRec ic
>        -> ChAttsRec (DefsR att nts vals ic)


Si el registro est\'a vac\'io no se inserta ninguna definici\'on:

> instance Defs att nts '[] ic where
>   type DefsR att nts '[] ic = ic
>   defs _ _ _ ic = ic

En el caso recursivo, combinamos la primer componente del registro
con la llamada recursiva.

> instance ( Defs att nts vs ic
>          , ic' ~ DefsR att nts vs ic
>          , HMember t nts
>          , HMemberRes t nts ~ mnts
>          , HasLabelChildAttsRes (lch,t) ic' ~ mch
>          , HasLabelChildAtts (lch,t) ic'
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

En todos los casos las funciones auxiliares utilizadas en la
cl\'ausula {\tt let} son funciones de acceso o predicados relativamente
simples de definir. Nuevamente se retornan valores necesarios para
tomar decisiones a nivel de tipos, porque la funci\'on es de tipos
dependientes. {\tt lch}, {\tt mch}, {\tt mnts} no tienen informaci\'on
a nivel de valores.
Por ejemplo {\tt hasLabelChildAtts} predica
la existencia de una etiqueta de hijo a nivel de tipos. Se define como
familia de tipos y a nivel de valores y se retorna un proxy.

> class HasLabelChildAtts (e :: k)(r :: [(k,[(k,Type)])]) where
>   type HasLabelChildAttsRes (e::k)(r :: [(k,[(k,Type)])]) :: Bool
>   hasLabelChildAtts
>    :: Label e -> ChAttsRec r -> Proxy (HasLabelChildAttsRes e r)

> instance HasLabelChildAtts e '[] where
>   type HasLabelChildAttsRes e '[] = 'False
>   hasLabelChildAtts _ _ = Proxy

> instance HasLabelChildAtts k ( '(k' ,v) ': ls) where
>   type HasLabelChildAttsRes k ( '(k' ,v) ': ls)
>       = Or (k == k') (HasLabelChildAttsRes k ls)
>   hasLabelChildAtts _ _ = Proxy


Notar que el contenido computacional de la definici\'on existe solo
a nivel de tipos, a nivel de valores la funci\'on tan solo propaga evidencia.

{\tt Or} es una funci\'on definida puramente a nivel de tipos,
y la implementamos como familia.

> type family Or (l :: Bool)(r :: Bool) :: Bool where
>   Or False b = b
>   Or True b  = 'True



\subsection{Aspectos}

Un aspecto se implementa
simplemente como un registro heterogeneo (que contendr\'a reglas
etiquetadas por nombres de producciones).
En este caso no consideramos
necesaria une implementaci\'on especializada y preferimos
reutilizar c\'odigo, en contraste a la implementaci\'on de las
atribuciones y registros de atribuciones de los hijos,
en donde la estructura es compleja e induce a errores de programaci\'on
(por lo que prefer\'iamos tipar lo m\'as fuertemente posible).
De cualquier manera, para el usuario de la biblioteca la
construcci\'on de malas instancias puede ser prohibida por constructores
inteligentes. En particular al utilizar el combinador de aspectos
se utiliza la funci\'on {\tt comSingle} que solo compila si las reglas
est\'an bien formadas, como vemos m\'as adelante.

> type Aspect = Record
> type Prd prd rule = Tagged prd rule

\subsection{Combinaci\'on de Aspectos}

La combinaci\'on de aspectos viene dada por la funci\'on {\tt (.+.)}
definida a nivel de tipos como la clase {\tt Com}.

> class Com (r :: [(k,Type)]) (s :: [(k, Type)]) where
>   type (.++.) r s :: [(k,Type)]
>   (.+.) :: Aspect r -> Aspect s -> Aspect (r .++. s)

La funci\'on inserta en el resultado intactas las producciones que aparecen
en un solo aspecto par\'ametro. Por otro lado las
producciones que aparezcan en ambos aspectos deber\'an incluirse
con las reglas combinadas (seg\'un la funci\'on {\tt ext} definida
previamente).
La funci\'on de combinaci\'on viene definida por recursi\'on en la
segunda componente. Si el segundo registro es vac\'io,
en la operaci\'on es neutro.

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
Si ya existe una producci\'on con ese nombre de deben combinar las reglas
en el campo correspondiente del aspecto, sino, el Aspecto debe extenderse.
Implementamos {\tt ComSingle} con un par\'ametro booleano extra que indica
la pertenencia o no de la etiqueta {\tt prd} al registro {\tt r}
La firma viene dada por:

> class ComSingle (b::Bool) (prd :: k) (rule :: Type) (r :: [(k,Type)]) where
>   type ComSingleR b prd rule r :: [(k, Type)]
>   comSingle :: Proxy b -> Prd prd rule -> Aspect r
>             -> Aspect (ComSingleR b prd rule r)


Nuevamente hacemos uso del proxy para propagar pruebas.
{\tt hasLabelRec} se define an\'alogamente a {\tt hasLabelChildAtts}.

Luego podemos definir las instancias posibles de {\tt ComSingle}, y adem\'as
chequeamos ciertas propiedades. En particular cuando combinamos reglas
chequeamos que efectivamente estamos combinando reglas.

> instance ( LabelSet ('(prd, rule) ': r)) => 
>   ComSingle 'False prd rule r where
>   type ComSingleR 'False prd rule r = '(prd, rule) ': r
>   comSingle _ prd asp = prd .*. asp

> instance ( UpdateAtLabelRecF prd (Rule sc ip ic  sp  ic'' sp'') r
>          , HasFieldRec prd r
>          , LookupByLabelRec prd r ~ (Rule sc ip ic' sp' ic'' sp'')
>          , ic'' ~ (Syn3 (LookupByLabelRec prd r))
>          , sp'' ~ (Inh3  (LookupByLabelRec prd r))
>          ) =>
>   ComSingle 'True prd (Rule sc ip ic  sp  ic'  sp') r where
>   type ComSingleR 'True prd (Rule sc ip ic  sp  ic'  sp') r
>     = UpdateAtLabelRecFR prd (Rule sc ip ic sp (Syn3 (LookupByLabelRec prd r))
>                                                (Inh3 (LookupByLabelRec prd r))) r
>   comSingle _ f r = updateAtLabelRecF l (oldR `ext` newR) r 
>     where l    = labelPrd f
>           oldR = lookupByLabelRec l r
>           newR = rulePrd f


Donde {\tt Syn3} e {\tt Inh3} son funciones definidas
puramente a nivel de tipos que implementan proyecciones.

> type family Syn3 (rule :: Type) :: [(k', [(k, Type)])] where
>   Syn3 (Rule sc ip ic  sp  ic'' sp'') = ic''
> type family Inh3 (rule :: Type) :: [(k, Type)] where
>   Inh3 (Rule sc ip ic  sp  ic'' sp'') = sp''



\subsection{Funciones sem\'anticas}

En cada producci\'on, llamamos \emph{funci\'on sem\'antica} al mapeo de los
atributos heredados a los atributos sintetizados. Una
computaci\'on sobre la gram\'atica
consiste en exactamente computar las funciones sem\'anticas.

En el ejemplo {\tt repmin}, la funci\'on {\tt sem\_Tree} construye,
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
porque eventualmente la gram\'atica podr\'ia extenderse con nuevas
producciones.


\subsection{La funci\'on {\tt knit}}

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


> class Kn (fcr :: [(k, Type)]) where
>   type ICh fcr :: [(k, [(k, Type)])]
>   type SCh fcr :: [(k, [(k, Type)])]
>   kn :: Record fcr -> ChAttsRec (ICh fcr) -> ChAttsRec (SCh fcr)

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
