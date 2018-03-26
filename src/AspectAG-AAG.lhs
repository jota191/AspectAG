> {-# LANGUAGE TypeInType,
>              GADTs,
>              KindSignatures,
>              TypeOperators,
>              TypeFamilies,
>              MultiParamTypeClasses,
>              FlexibleInstances,
>              FlexibleContexts,
>              StandaloneDeriving,
>              UndecidableInstances,
>              FunctionalDependencies,
>              ConstraintKinds,
>              ScopedTypeVariables,
>              AllowAmbiguousTypes,
>              UnicodeSyntax#-}

> module AspectAG where


> import HList hiding (Apply,apply)
> import Data.Kind

Attributions are mappings from Attribute names to attribute values
implemented as a Record

> type Att att val = Tagged att val

Labels are purely phantom



Input and output families of information flow are represented as

> data Fam (c :: [Type]) (p::[Type]) :: Type where
>   Fam :: Record c -> Record p -> Fam c p

< data Fam c p = Fam c p

> type Chi ch atts = Tagged ch atts

> labelChi :: Chi ch atts -> Label ch
> labelChi = labelLVPair

Rules, aka definition of attribution computations
Rules are defined as a mapping from an input family to an output family,
the added arity is for make them composable

> type Rule sc ip ic sp ic' sp'
>   = Fam sc ip -> (Fam ic sp -> Fam ic' sp')

--composition

> ext :: Rule sc ip ic' sp' ic'' sp''
>     -> Rule sc ip ic sp ic' sp'
>     -> Rule sc ip ic sp ic'' sp''

> (f `ext` g) input = f input . g input


Definition of a synthesized attribute

> syndef :: (HExtend Record (Att att val) sp,
>            sp' ~ HExtendR Record (Att att val) sp)
>           => Label att -> val -> (Fam ic sp -> Fam ic sp')
> syndef att val (Fam ic sp) = Fam ic (att .=. val .*. sp)


> synmod  ::  (HUpdateAtLabel att val sp sp',
>              SameLength sp sp')--, HasField att sp' val)
>        =>  Label att -> val -> Fam ic sp -> Fam ic sp'
> synmod att v (Fam ic sp) = Fam ic (hUpdateAtLabel att v sp)


 The function 'inhdef' introduces a new inherited attribute for
a collection of non-terminals.
It takes the following parameters:
   'att': the attribute which is being defined,
   'nts': the non-terminals with which this attribute is being associated, and
   'vals': a record labelled with child names and containing values,
            describing how to compute the attribute being defined at each
            of the applicable child  positions.
 It builds a function which updates the output constructed thus far.||


> inhdef  ::  Defs att nts vals ic ic'
>         => Label att -> HList nts -> Record vals -> (Fam ic sp -> Fam ic' sp)
> inhdef att nts vals (Fam ic sp) =
>         Fam (defs att nts vals ic) sp


Defs is defined inductively over the record vals containing
the new definitions

> class Defs att (nts :: [Type]) (vals :: [Type])
>            (ic :: [Type]) (ic' :: [Type]) where
>   defs :: Label att -> HList nts -> Record vals
>        -> Record ic -> Record ic'


> instance Defs att nts '[] ic ic where
>   defs _ _ _ ic = ic


> 
> instance ( Defs att nts vs ic ic'
>          , HasLabel (Label(Label (lch,t))) ic' mch
>          , HMember (Label t) nts mnts
>          , SingleDef mch mnts att
>            (Chi (Label (lch,t)) vch)
>            ic' ic''
>          )
>  => Defs att nts ((Chi (Label (lch,t)) vch) ': vs) ic ic'' where
>   defs att nts (Record (HCons pch vs)) ic
>     = singledef mch mnts att pch (ic' :: Record ic')
>             -- estuve bastante trancado aca,
>             -- anotar este tipo fue la solucion para
>             -- que el type checker unificara el parametro con el contexto
>             -- ojo que tengo tipos ambiguos activados para que funcione!
>       where ic'  = defs att nts (Record vs) ic
>             lch  = labelLVPair pch
>             mch  = hasLabel lch ic'
>             mnts = hMember (sndUnwrap lch) nts
> 


> sndUnwrap :: Label (Label (a,b)) -> Label b
> sndUnwrap _ = undefined


> class SingleDef
>  (mch :: Bool) (mnts::Bool) (att::k) pv (ic :: [Type]) (ic' :: [Type])
>    | mch mnts att pv ic -> ic'   where
>   singledef :: Proxy mch -> Proxy mnts -> Label att -> pv
>             -> Record ic -> Record ic'

> instance  ( HasField lch ic (Record och) --och es el record
>                                          --sacandole el wrapper
>           , HExtendR Record (Att att vch) och ~ och'
>           , HLabelSet (Label att : LabelsOf och)
>           , HUpdateAtLabel lch (Record och') ic ic'
>           , SameLength ic ic'
>           , HAllTaggedLV och) 
>       => SingleDef True True att (Chi lch vch) ic ic'
>   where singledef _ _ att pch ic =
>            hUpdateAtLabel lch (att .=. vch .*. och) ic
>            where  lch  = labelLVPair pch
>                   vch  = valueLVPair pch
>                   och  = hLookupByLabel lch ic





Falta implementar cosas aca, inhmod y tal, lleva tiempo pero no deberia de
generar grandes complicaciones.

Voy a jugar un rato con unicode

> type 𝔹 = Bool


ASPECTS

Aspects son records que contienen una regla para cada produccion

> type Prd prd rule = Tagged prd rule
> -- ver si hago algun setter, getter
> labelPrd = labelLVPair
> rulePrd  = valueLVPair


> type Aspect = Record

Combinacion de aspects:

> class Com (r₁ ∷ [Type]) (r₂ ∷ [Type]) (r₃ ∷ [Type]) | r₁ r₂ → r₃ where
>   (⊕) ∷ Aspect r₁ → Aspect r₂ → Aspect r₃


Definimos por induccion la combinacion de aspectos.

La idea es unirlos, y si hay etiquetas compartidas en uno y otro, combinamos las
reglas con la funcion ext.

Primero definimos comSingle, para combinar una regla con un record. Como hay que
"decidir segun el contexto" la instancia a usar, usamos un parametro booleano
extra (la tecnica de siempre)


> class ComSingle (b ∷ 𝔹) f (r₁ ∷ [Type]) (r₂ ∷ [Type]) | b f r₁ → r₂ where
>   comSingle ∷ Proxy b → f → Record r₁ → Record r₂

TODO: f es un Tagged (Prd p r),
cuando itere de nuevo en el codigo quiero ver si
rinde expresarlo aca

b vale True si el label de f aparece en el record,
vamos con el caso en que no primero, que es el mas facil

> instance ComSingle 'False (f ∷ Type) (r ∷ [Type]) (f ': r ∷ [Type]) where
>   comSingle _ f (Record r) = Record (HCons f r)

Ahora el caso en que las etiquetas coinciden y hay que mergear reglas:

> instance (HasField prd r (Rule sc ip ic' sp' ic'' sp'')
>          ,HUpdateAtLabel prd (Rule sc ip ic sp ic'' sp'') r r'
>          ,SameLength r r')
>   ⇒ ComSingle 'True
>                (Prd prd (Rule sc ip ic sp ic' sp'))
>                (r ∷ [Type])
>                (r'∷ [Type]) where
>   comSingle _ f r = hUpdateAtLabel l (oldR `ext` newR) r
>     where l    = labelPrd f
>           oldR = r # l
>           newR = rulePrd f


Ahora si defino com, por induccion sobre el primer Record

> instance Com r '[] r where
>   r ⊕ Record HNil = r

>
> instance ( HasLabel prd r₁ b,
>           ComSingle b (Prd prd rule) r₁ rcomsingle
>          , Com rcomsingle r₂ r₃
>          ) ⇒
>    Com r₁ (Prd prd rule ': r₂) r₃ where
>   r₁ ⊕ Record (HCons prd r₂) = r₃
>     where b     = hasLabel2 (labelPrd prd) r₁ ∷ Proxy b
>           rcomS = comSingle b prd r₁ ∷ Record rcomsingle
>           r₃    = rcomS ⊕ (Record r₂) ∷ Record r₃
>

TODO: ESTO NO ESTA FUNCIONANDO CON LA FUNDEP ###FIXED
TODO: haslabel y haslabel2 tienen funcion analoga,

< hasLabel :: HasLabel l r b => l -> Record r -> Proxy b
< hasLabel2 :: HasLabel l r b => Label l -> Record r -> Proxy b

habria que ver como unificar. hasLabel2 es mas correcto
(de hecho el tipo de l es kind polimorfico
y no tiene por que tener habitantes)

> {-

A ver con una Type family
El parametro booleano es si hago merge o no

> class Com₂ (b ∷ 𝔹)(r₁ ∷ [Type]) (r₂ ∷ [Type]) where
>   type Com₂R (b ∷ 𝔹) r₁ r₂ :: [Type]
>   com ∷ Proxy b → Aspect r₁ → Aspect r₂ → Aspect (Com₂R b r₁ r₂)

> instance Com₂ 'False r₁ '[] where
>   type Com₂R 'False r₁ '[] = r₁
>   com _ r₁ (Record HNil) = r₁

> instance ( HasLabel prd r₁ b
>          , ComSingle 'False (Prd prd rule) r₁ rcomSingle
>          , Com₂R b rcomSingle r₂ ~ r₃
>          )
>   => Com₂ 'False r₁ (Prd prd rule ': r₂) where
>   type Com₂R 'False r₁ (Prd prd rule ': r₂) = r₃

ESTAS COSAS NUNCA FUNCIONAN

The RHS of an associated type declaration mentions ‘r₃’
      All such variables must be bound on the LHS

> -}


KNIT function

fc → functions of the children
ic → inputs of the children
sc → results of the children

Kn es un zipwith$ a nivel de tipos

> class KnList (fc ∷ [Type]) (ic ∷ [Type]) (sc ∷ [Type]) | fc → ic sc where
>   knList ∷ HList fc → HList ic → HList sc

> class Kn (fc ∷ [Type]) (ic ∷ [Type]) (sc ∷ [Type]) | fc → ic sc where
>   kn ∷ Record fc → Record ic → Record sc

TODO: hay que abstraer mas aca, estoy usando records, en vez de atributions,
ir al siguiente TODO

> instance KnList '[] '[] '[] where
>   knList _ _ = HNil


> instance (KnList fc ic sc)
>   ⇒ KnList (Chi lch (ich → sch) ': fc)
>            (Chi lch     ich     ': ic)
>            (Chi lch     sch     ': sc) where
>   knList (HCons pfch fcr) (HCons pich icr)
>     = (newLVPair lch (fch ich)) .*. (knList fcr icr)
>     where lch = labelChi pfch
>           fch = valueLVPair pfch
>           ich = valueLVPair pich

TODO: hay que ELIMINAR valueLVPair y labelLVPair, y hacer una interfaz de Tagged
para cada cosa, abstrayendonos de que son Taggeds

(ipor ej. un modulo utils con estas cosas, opacando la implementacion)

> instance ( HAllTaggedLV sc
>          , HLabelSet (LabelsOf sc)
>          , KnList fc ic sc)
>   ⇒ Kn fc ic sc where
>   kn (Record fcr)(Record icr) = mkRecord $ knList fcr icr




EMPTIES

> class EmptiesList (fc ∷ [Type]) (ec ∷ [Type]) | fc → ec where
>   emptiesList ∷ HList fc → HList ec


> instance EmptiesList '[] '[] where
>   emptiesList HNil = HNil


> instance EmptiesList fc ec
>   ⇒ EmptiesList (Chi lch fch ': fc) (Chi lch (Record '[]) ': ec) where
>   emptiesList (HCons pch fcr) = newLVPair lch emptyRecord .*. emptiesList fcr
>     where lch = labelLVPair pch



TODO: Copy Rules, etc













Definiendo Aspectos

inhAspect toma un atributo, una lista de no terminales,
en donde el atributo esta definido, la lista cpys de producciones en donde
la copy rule esta aplicada, y un record defs que tiene las definiciones
explicitas de producciones

> -- inhAspect att nts cpys defs
> --   = defAspect





Instancias de Apply

< data FnSyn att = FnSyn att

< 
< instance {-(ctx) => -}
<   Apply  (FnSyn att) (Fam sc ip -> val)  where
<   type ApplyR (FnSyn att) (Fam sc ip -> val)
<     = forall ic sp.
<     (Rule sc ip ic sp ic (Tagged att val ': sp))
<   apply (FnSyn att) f =  syndef att . f
< 

TODO: hacer un diagrama conmutativo con el tipado de esto en la documentacion



El problema con apply:

Esto funcionaba bien con la implementacion vieja debilmente tipada.
Aca no es el caso.
Apply Construye un t\'ermino de tipo

< Rulesc ip ic sp ic sp'@(Tagged att val ': sp).

El problema es que tengo variables
"libres" en este tipo (sp, ic) pero la construccion Apply no las admite

Si construyo Apply con fundep falla la condicion de cubrimiento,
Si usoel tipo indizado ApplyR, no le puedo pasar esos tipos como parametro.

Tampoco puedo cuantificar universalmente sp e ic por el kind que tienen([Type])





Solucion1: Hacer un apply "a medida" pasando parametros

Solucion2: Obviar la dependencia funcional
(y rezar para que el compilador se arregle sin eso...)

Vamos por la 2..

------------



> class Apply f a r {-| f a -> r-}  where
>   apply :: f -> a -> r


> instance ( HAllTaggedLV sp
>          , HExtendR Record (Tagged att val) sp ~ sp'
>          , HLabelSet (Label att : LabelsOf sp))
>            =>
>   Apply (FnSyn att) (Fam sc ip -> val)
>         (Rule sc ip ic sp ic sp') where
>   apply (FnSyn _) f =  syndef (Label :: Label att) . f


> data FnInh att (nt :: [Type]) where
>   FnInh ::  Label att -> HList nt -> FnInh att nt

> instance Defs att (nts::[Type])(vals:: [Type])(ic:: [Type])(ic' :: [Type])
>   => Apply (FnInh att nts) (Fam sc ip -> Record vals)
>            (Rule sc ip ic sp ic' sp) where
>   apply (FnInh att nts) f = inhdef att nts . f



> class TypeCast x y | x -> y, y -> x where
>   typeCast :: x -> y

> instance TypeCast t t where
>   typeCast = id

> class Poly a b where
>   poly :: a -> b



Hay que reescribir esto:

> {-
> instance  (  Copy att nts vp ic ic'
>           ,  HasField att ip vp
>           ,  TypeCast (Rule sc ip ic sp ic' sp) r) 
>          => Poly  (FnCpy att nts) r  where 
>   poly (FnCpy att nts)  = typeCast $ copy att nts 
> -}

> instance  ( HAllTaggedLV sp
>           , Use att nts a sc
>           , HExtendR Record (Tagged att a) sp ~ sp'
>           , HLabelSet (Label att : LabelsOf sp)
>           , TypeCast (Rule sc ip ic sp ic sp') r) 
>          => Poly  (FnUse att nts (a -> a -> a) a) r where 
>   poly (FnUse att nts op unit)  = typeCast $ use att nts op unit 


-- | A /use/ rule declares a synthesized attribute that collects information
--   from some of the children.
--   The function 'use' takes the following arguments: the attribute to be
defined, 
--   the list of non-terminals for which the attribute is defined,
--   a monoidal operator which combines the attribute values, 
--   and a unit value to be used in those cases where none of 
--   the children has such an attribute. 

> use  ::  ( HAllTaggedLV sp
>          , HLabelSet (Label att : LabelsOf sp)
>          , Use att nts a sc
>          , HExtendR Record (Att att a) sp ~ sp')
>      =>  Label att -> HList nts -> (a -> a -> a) -> a
>          -> Rule sc ip ic sp ic sp'

> use att nts oper unit (Fam sc _) = syndef att val where
>   val = case usechi att nts oper sc of
>           Just r  -> r
>           Nothing -> unit


> class Use att (nts :: [Type]) a (sc :: [Type])  where
>   usechi :: Label att -> HList nts -> (a -> a -> a) -> Record sc -> Maybe a

> --instance Use att nts a sc => Use att nts a (HList sc) where
> --  usechi att nts oper (Record sc) = usechi att nts oper sc

> instance Use l nt a '[] where
>   usechi _ _ _ _ = Nothing

> instance ( HMember (Label t) nts mnts
>          , Use' mnts att nts a ((Tagged (Label (lch, t)) vch) ': scr))
>   => Use att nts a ((Tagged (Label (lch, t)) vch) ': scr) where
>   usechi att nts oper sc@(Record (HCons fa _))
>     = usechi' mnts att nts oper sc
>     where mnts = hMember (sndUnwrap $ labelLVPair fa) nts

> class Use' (mnts :: Bool)
>            (att :: k)
>            (nts :: [Type])
>             a
>             (sc :: [Type]) where
>  usechi' :: Proxy mnts -> Label att -> HList nts
>         -> (a -> a -> a) -> Record sc -> Maybe a

> instance (HasField att vch a, Use att nts a scr)  => 
>          Use' 'True att nts a ((Tagged lch (Record vch)) ': scr) where
>   usechi' _ att nts oper (Record(HCons fa scr))
>     = Just $ case usechi att nts oper (Record scr) of
>                Just r  -> oper (valueLVPair fa # att) r
>                Nothing -> valueLVPair fa # att

> instance (Use att nts a scr)
>   => Use' 'False att nts a ((Tagged lch b) ': scr) where
>   usechi' _ att nts oper (Record(HCons _ scr))
>     = usechi att nts oper (Record scr)



Aspectos por defecto
Construye un aspecto dada una regla y una lista de producciones

> class DefAspect (deff :: Type) (prds :: [Type]) (rules :: [Type]) where
>   defAspect :: deff -> HList prds -> Record rules

> instance DefAspect (deff :: Type) '[] '[] where
>   defAspect _ _ = emptyRecord

> --instance DefAspect....
> instance ( Poly deff deff'
>          , HAllTaggedLV (Prd prd deff' ': rules)
>          , HLabelSet (Label prd : LabelsOf rules)
>          , HExtendR Record (Prd prd deff') rules ~ rules'
>          , DefAspect deff prds rules)
>    => DefAspect deff (Label prd ': prds) rules' where
>   defAspect deff (HCons prd prds) =
>     prd .=. poly deff .*. defAspect deff prds




Attribute aspects

La funcion attAspect actualiza todos los valores de un Record aplicandoles
una funcion

> class AttAspect (rdef :: Type) (defs :: [Type]) (rules :: [Type])
>       {-| rdef defs -> rules-} where
>   attAspect :: rdef -> Record defs -> Record rules

> instance AttAspect rdef '[] '[] where
>   attAspect _ _ = emptyRecord

> instance ( AttAspect rdef defs rules
>          , Apply (FnSyn rdef) def rule -- ???
>          , HExtendR Record (Prd lprd rule) rules ~ rules'
>          , HAllTaggedLV defs
>          , HLabelSet (Label lprd : LabelsOf rules)
>          , HAllTaggedLV rules
>          , HLabelSet (LabelsOf defs))
>   => AttAspect rdef (Prd lprd def ': defs) rules' where
>   attAspect rdef (Record (HCons def defs)) =
>     ((labelLVPair def) .=. ((apply (FnSyn (Label ::Label rdef))
>                              (valueLVPair def)) :: rule))
>     .*. attAspect rdef (mkRecord defs) :: Record rules'


-- | The function 'inhAspect' defines an inherited attribute aspect.
--   It takes as arguments: the name of the attribute 'att', 
--   the list 'nts' of non-terminals where the attribute is defined,
--   the list 'cpys' of productions where the copy rule has to be applied, 
--   and a record 'defs' containing the explicit definitions for some productions.

> --inhAspect ::  (  AttAspect (FnInh att nts) defs defasp
> --              ,  DefAspect (FnCpy att nts) cpys cpyasp
> --              ,  Com cpyasp defasp inhasp)
> --         => att -> nts -> cpys -> defs -> inhasp
> --inhAspect att nts cpys defs
> --   =     (defAspect  (FnCpy att nts)  cpys)
> --   .+.   (attAspect  (FnInh att nts)  defs)


-- | The function 'synAspect' defines a synthesized attribute aspect.
---  The rule applied is the use rule,
--   which takes 'op' as the monoidal operator and 'unit' as the unit value.

> {-
> synAspect ::  (  AttAspect (FnSyn att) defs defasp
>               ,  DefAspect (FnUse att nts op unit) uses useasp
>               ,  Com useasp defasp synasp)
>           => Label att
>           -> HList nts
>           -> op
>           -> unit
>           -> HList uses
>           -> Record defs
>           -> Aspect synasp
> synAspect (att :: Label att) (nts :: HList nts) (op :: op)
>           (unit :: unit) (uses :: HList uses) (defs::Record defs)
>    =(((defAspect (FnUse att nts op unit) uses) :: Record useasp)
>      ⊕
>     ((attAspect (FnSyn att) defs) :: Aspect defasp)) :: Aspect synasp

> class SynAspect -- ....

> -}

NO COMPILA:

AspectAG.lhs:510:8: error:
    • Could not deduce (Com r₁0 r₂0 synasp1) arising from a use of ‘⊕’
      from the context: (AttAspect (FnSyn att) defs defasp,
                         DefAspect (FnUse att nts op unit) uses useasp,
                         Com useasp defasp synasp)
        bound by the type signature for:
                   synAspect :: (AttAspect (FnSyn att) defs defasp,
                                 DefAspect (FnUse att nts op unit) uses useasp,
                                 Com useasp defasp synasp) =>
                                Label att
                                -> HList nts
                                -> op
                                -> unit
                                -> HList uses
                                -> Record defs
                                -> Aspect synasp
        at AspectAG.lhs:(498,3)-(507,28)
      The type variables ‘r₁0’, ‘r₂0’ are ambiguous
      These potential instances exist:
        two instances involving out-of-scope types
          instance forall k (prd :: k) (r₁ :: [Type]) (b :: Bool) rule (rcomsingle :: [Type]) (r₂ :: [Type]) (r₃ :: [Type]).
                   (HasLabel prd r₁ b, ComSingle b (Prd prd rule) r₁ rcomsingle,
                    Com rcomsingle r₂ r₃) =>
                   Com r₁ (Prd prd rule : r₂) r₃
            -- Defined at AspectAG.lhs:222:12
          instance Com r '[] r -- Defined at AspectAG.lhs:218:12
    • In the expression:
          (((defAspect (FnUse att nts op unit) uses) :: Record useasp)
           ⊕ ((attAspect (FnSyn att) defs) :: Aspect defasp)) ::
            Aspect synasp
      In an equation for ‘synAspect’:
          synAspect
            (att :: Label att)
            (nts :: HList nts)
            (op :: op)
            (unit :: unit)
            (uses :: HList uses)
            (defs :: Record defs)
            = (((defAspect (FnUse att nts op unit) uses) :: Record useasp)
               ⊕ ((attAspect (FnSyn att) defs) :: Aspect defasp)) ::
                Aspect synasp

AspectAG.lhs:510:10: error:
    • Could not deduce (DefAspect (FnUse att nts op unit) uses useasp1)
        arising from a use of ‘defAspect’
      from the context: (AttAspect (FnSyn att) defs defasp,
                         DefAspect (FnUse att nts op unit) uses useasp,
                         Com useasp defasp synasp)
        bound by the type signature for:
                   synAspect :: (AttAspect (FnSyn att) defs defasp,
                                 DefAspect (FnUse att nts op unit) uses useasp,
                                 Com useasp defasp synasp) =>
                                Label att
                                -> HList nts
                                -> op
                                -> unit
                                -> HList uses
                                -> Record defs
                                -> Aspect synasp
        at AspectAG.lhs:(498,3)-(507,28)
    • In the first argument of ‘(⊕)’, namely
        ‘((defAspect (FnUse att nts op unit) uses) :: Record useasp)’
      In the expression:
          (((defAspect (FnUse att nts op unit) uses) :: Record useasp)
           ⊕ ((attAspect (FnSyn att) defs) :: Aspect defasp)) ::
            Aspect synasp
      In an equation for ‘synAspect’:
          synAspect
            (att :: Label att)
            (nts :: HList nts)
            (op :: op)
            (unit :: unit)
            (uses :: HList uses)
            (defs :: Record defs)
            = (((defAspect (FnUse att nts op unit) uses) :: Record useasp)
               ⊕ ((attAspect (FnSyn att) defs) :: Aspect defasp)) ::
                Aspect synasp

AspectAG.lhs:512:9: error:
    • Could not deduce (AttAspect (FnSyn att) defs defasp1)
        arising from a use of ‘attAspect’
      from the context: (AttAspect (FnSyn att) defs defasp,
                         DefAspect (FnUse att nts op unit) uses useasp,
                         Com useasp defasp synasp)
        bound by the type signature for:
                   synAspect :: (AttAspect (FnSyn att) defs defasp,
                                 DefAspect (FnUse att nts op unit) uses useasp,
                                 Com useasp defasp synasp) =>
                                Label att
                                -> HList nts
                                -> op
                                -> unit
                                -> HList uses
                                -> Record defs
                                -> Aspect synasp
        at AspectAG.lhs:(498,3)-(507,28)
    • In the second argument of ‘(⊕)’, namely
        ‘((attAspect (FnSyn att) defs) :: Aspect defasp)’
      In the expression:
          (((defAspect (FnUse att nts op unit) uses) :: Record useasp)
           ⊕ ((attAspect (FnSyn att) defs) :: Aspect defasp)) ::
            Aspect synasp
      In an equation for ‘synAspect’:
          synAspect
            (att :: Label att)
            (nts :: HList nts)
            (op :: op)
            (unit :: unit)
            (uses :: HList uses)
            (defs :: Record defs)
            = (((defAspect (FnUse att nts op unit) uses) :: Record useasp)
               ⊕ ((attAspect (FnSyn att) defs) :: Aspect defasp)) ::
                Aspect synasp


Lo anterior no esta compilando, defino la funcion por recursion




> {- Esto tampoco va a funcionar
> inhAspect ::  (  AttAspect (FnInh att nts) defs defasp
>               ,  DefAspect (FnCpy att nts) cpys cpyasp
>               ,  Com cpyasp defasp inhasp)
>          => Label att
>           -> HList nts
>           -> HList cpys
>           -> Record defs
>           -> Aspect inhasp
> inhAspect att nts cpys defs
>    = (defAspect  (FnCpy att nts)  cpys)
>    ⊕ (attAspect  (FnInh att nts)  defs)

> -}

> class InhAspect att
>                (nts::[Type])
>                (cpys::[Type])
>                (defs::[Type])
>                (inhasp::[Type]) where
>   inhAspect ::  Label att
>              -> HList nts
>              -> HList cpys
>              -> Record defs
>              -> Aspect inhasp

Con una clase cubro todo:

> instance ( AttAspect (FnInh att nts) defs defasp
>          , DefAspect (FnCpy att nts) cpys cpyasp
>          , Com cpyasp defasp inhasp)
>    => InhAspect att
>                (nts::[Type])
>                (cpys::[Type])
>                (defs::[Type])
>                (inhasp::[Type]) where
>   inhAspect att nts cpys defs
>     = (((defAspect  (FnCpy att nts)  cpys) :: Aspect cpyasp)
>     ⊕ ((attAspect  (FnInh att nts)  defs):: Aspect defasp):: Aspect inhasp)

La funcion tiene que estar en una typeclass para que tipe,
no hay necesidad de definir una recursion con la type class, solo enmarcarla,
esta definicion es identica a la version en top level que no compilaba





> class SynAspect att
>                (nts::[Type])
>                op
>                unit
>                (uses :: [Type])
>                (defs::[Type])
>                (synasp ::[Type])where
>   synAspect :: Label att
>             -> HList nts
>             -> op
>             -> unit
>             -> HList uses
>             -> Record defs
>             -> Aspect synasp

> instance (  AttAspect (FnSyn att) defs defasp
>          ,  DefAspect (FnUse att nts op unit) uses useasp
>          ,  Com useasp defasp synasp)
>           => SynAspect att nts op unit uses defs synasp where
>   synAspect att nts op unit uses defs
>     = (((defAspect (FnUse att nts op unit) uses) :: Record useasp)
>     ⊕ ((attAspect (FnSyn att) defs) :: Aspect defasp)) :: Aspect synasp



> data FnCpy' att nts = FnCpy' att nts
> data FnCpy att (nts::[Type]) :: Type where
>   FnCpy :: Label att -> HList nts -> FnCpy att nts


> data FnUse att (nt::[Type]) op unit :: Type where
>   FnUse :: Label att -> HList nt -> op -> unit -> FnUse att nt op unit


> data FnSyn att :: Type where
>   FnSyn :: Label att -> FnSyn att


> data FnUse' att nt op unit = FnUse' att nt op unit
> data FnSyn' att = FnSyn' att



