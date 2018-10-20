\subsection{Implementaci\'on}

Como dijimos antes,
una atribuci\'on (\emph{attribution}) es un mapeo de nombres de atributos
(que son represenentados puramente a nivel de tipos como etiquetas)
a sus valores. La estructura de Registro extensible (fuertemente tipado)
presentada anteriormente es ideal para representarles.

Para obtener mensajes de error precisos y evitar que se filtre
implementaci\'on en los mismos, decidimos tener estructuras especializadas.

[explicar mejor]

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
Esto es para soportar la generaci\'on de etiquetas por parte del
programador a nivel de valores y usar los kinds promovidos.

Dado que una atribuci\'on una vez bajo
el wrapper {\tt Attrribution} tiene kind {\tt Type}, podr\'iamos haber
implementado a los hijos como un record agn\'ostico respecto al contenido.
Se prefiere una implementaci\'on fuertemente tipada sobre reutilizar
el c\'odigo existente.


En cada nodo de la gram\'atica, una \emph{Familia} contiene la atribuci\'on
del padre y la colecci\'on de atribuciones de los hijos.

> data Fam (c::[(k,[(k,Type)])]) (p :: [(k,Type)]) :: Type where
>   Fam :: ChAttsRec c  -> Attribution p -> Fam c p

Una regla es una funci\'on de la familia de entrada a la de salida,
el tipo de las reglas se implementa con una aridad extra para hacerlas
componibles, como en [REF]

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
