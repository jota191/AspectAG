{-# OPTIONS -XMultiParamTypeClasses -XFunctionalDependencies 
            -XFlexibleContexts -XFlexibleInstances 
            -XUndecidableInstances 
            -XExistentialQuantification 
            -XEmptyDataDecls -XRank2Types
            -XTypeSynonymInstances #-}

{-| 
    Library for First-Class Attribute Grammars.

    The library is documented in the paper: /Attribute Grammars Fly First-Class. How to do aspect oriented programming in Haskell/


    For more documentation see the AspectAG webpage: 
    <http://www.cs.uu.nl/wiki/bin/view/Center/AspectAG>.
-}


module Data.AspectAG {-(

              -- * Rules
              Att, Fam(..), Chi, Rule, 
              inhdef, syndef, 
              inhmod, synmod,
              ext,

              -- ** Monadic
              At(..), lhs, def,
              inhdefM, syndefM,
              inhmodM, synmodM,

              -- * Aspects
              Prd, (.+.),

              -- * Semantic Functions
              sem_Lit, knit,

              -- * Common Patterns
              copy, use, chain,

              -- * Defining Aspects
             -- inhAspect, synAspect, chnAspect,
             -- attAspect, defAspect,

              module Data.HList
            )-} where

import Data.HList hiding ((.+.), hUpdateAtLabel)
import Data.HList.FakePrelude

import Control.Monad.Reader

-- | Field of an attribution.
type Att att val = LVPair att val

-- | A Family 'Fam' contains a single attribution 'p' for the parent and
--   a collection of attributions 'c' for the children. 
data Fam c p = Fam c p

-- | Field of the record of attributions for the children.
type Chi ch atts = LVPair ch atts

-- | The type 'Rule' states that a rule takes as input the synthesized attributes 
--   of the children 'sc' and the inherited attributes of the parent 'ip' and returns
--   a function from the output constructed thus far (inherited attributes of the children 
--   |ic| and synthesized attributes of the parent 'sp') to the extended output.
type Rule sc ip ic sp ic' sp' = Fam sc ip -> Fam ic sp -> Fam ic' sp'

-- | The function 'syndef' adds the definition of a synthesized attribute.
--   It takes a label 'att' representing the name of the new attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function which 
--   updates the output constructed thus far.
syndef  ::  HExtend (Att att val) sp sp'
        =>  att -> val -> (Fam ic sp -> Fam ic sp')
syndef  att val (Fam ic sp) = Fam  ic (att .=. val .*. sp)

-- | The function 'synmod' modifies the definition of a synthesized attribute.
--   It takes a label 'att' representing the name of the attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function which 
--   updates the output constructed thus far.
synmod  ::  HUpdateAtLabel att val sp sp' 
        =>  att -> val -> Fam ic sp -> Fam ic sp' 
synmod att v (Fam ic sp) = Fam ic (hUpdateAtLabel att v sp) 

-- | The function 'inhdef' introduces a new inherited attribute for 
--   a collection of non-terminals.
--   It takes the following parameters:
--     'att': the attribute which is being defined,
--     'nts': the non-terminals with which this attribute is being associated, and
--     'vals': a record labelled with child names and containing values, 
--              describing how to compute the attribute being defined at each 
--              of the applicable child  positions.
--   It builds a function which updates the output constructed thus far.||
inhdef  ::  Defs att nts vals ic ic' 
        =>  att -> nts -> vals -> (Fam ic sp -> Fam ic' sp)
inhdef att nts vals (Fam ic sp) = 
        Fam (defs att nts vals ic) sp


-- | The class 'Defs' is defined by induction over the record 'vals' 
--   containing the new definitions. 
--   The function 'defs' inserts each definition into the attribution 
--   of the corresponding child. 
class Defs att nts vals ic ic'  | vals ic -> ic' where
  defs :: att -> nts -> vals -> ic -> ic'

instance Defs att nts (Record HNil) ic ic where
  defs _ _ _ ic = ic

instance  ( Defs att nts (Record vs) ic ic'
          , HasLabel (Proxy (lch,t)) ic' mch
          , HMember (Proxy t) nts mnts
          , SingleDef  mch mnts att 
                  (Chi (Proxy (lch,t)) vch) 
                  ic' ic'' ) 
      => Defs  att nts 
               (Record (HCons  (Chi (Proxy (lch,t)) vch) vs)) 
               ic ic'' 
      where 
  defs att nts ~(Record (HCons pch vs)) ic = 
         singledef mch mnts att pch ic'  
         where  ic'     = defs att nts (Record vs) ic
                lch     = labelLVPair pch
                mch     = hasLabel lch ic'
                mnts    = hMember (sndProxy lch) nts


class  SingleDef mch mnts att pv ic ic' 
       | mch mnts pv ic -> ic' 
  where singledef :: mch -> mnts -> att -> pv -> ic -> ic'


data IncorrectDef l lch err
data UndefNT t
data UndefProd t
data UndefAtt t

instance Fail (IncorrectDef l lch (UndefNT t)) 
         => SingleDef HTrue HFalse (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singledef = undefined

instance Fail (IncorrectDef l lch (UndefProd (lch,t))) 
         => SingleDef HFalse HTrue (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singledef = undefined


instance  ( HasField lch ic och
          , HExtend (Att att vch) och och'
          , HUpdateAtLabel lch och' ic ic') 
      => SingleDef  HTrue HTrue att (Chi lch vch) ic ic' 
  where singledef _ _ att pch ic = 
           hUpdateAtLabel lch (att .=. vch .*. och) ic  
           where  lch  = labelLVPair  pch
                  vch  = valueLVPair  pch
                  och  = hLookupByLabel lch ic 




-- | The function 'inhmod' modifies an inherited attribute for 
--   a collection of non-terminals.
--   It takes the following parameters:
--     'att': the attribute which is being defined,
--     'nts': the non-terminals with which this attribute is being associated, and
--     'vals': a record labelled with child names and containing values, 
--              describing how to compute the attribute being defined at each 
--              of the applicable child  positions.
--   It builds a function which updates the output constructed thus far.||
inhmod  ::  Mods att nts vals ic ic' 
        =>  att -> nts -> vals -> (Fam ic sp -> Fam ic' sp)
inhmod att nts vals (Fam ic sp) = 
        Fam (mods att nts vals ic) sp



-- | The class 'Mods' is defined by induction over the record 'vals' 
--   containing the new definitions. 
--   The function 'mods' inserts each definition into the attribution 
--   of the corresponding child. 
class Mods att nts vals ic ic'  | vals ic -> ic' where
  mods :: att -> nts -> vals -> ic -> ic'

instance Mods att nts (Record HNil) ic ic where
  mods _ _ _ ic = ic

instance  ( Mods att nts (Record vs) ic ic'
          , HasLabel (Proxy (lch,t)) ic' mch
          , HMember (Proxy t) nts mnts
          , SingleMod  mch mnts att 
                  (Chi (Proxy (lch,t)) vch) 
                  ic' ic'' ) 
      => Mods  att nts 
               (Record (HCons  (Chi (Proxy (lch,t)) vch) vs)) 
               ic ic'' 
      where 
  mods att nts ~(Record (HCons pch vs)) ic = 
         singlemod mch mnts att pch ic'  
         where  ic'     = mods att nts (Record vs) ic
                lch     = labelLVPair pch
                mch     = hasLabel lch ic'
                mnts    = hMember (sndProxy lch) nts



class  SingleMod mch mnts att pv ic ic' 
       | mch mnts pv ic -> ic' 
  where singlemod :: mch -> mnts -> att -> pv -> ic -> ic'


data IncorrectMod l lch err

instance Fail (IncorrectMod l lch (UndefNT t)) 
         => SingleMod HTrue HFalse (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singlemod = undefined

instance Fail (IncorrectMod l lch (UndefProd (lch,t))) 
         => SingleMod HFalse HTrue (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singlemod = undefined


instance  ( HasField lch ic och
          , HUpdateAtLabel att vch och och'
          , HUpdateAtLabel lch och' ic ic') 
      => SingleMod  HTrue HTrue att (Chi lch vch) ic ic' 
  where singlemod _ _ att pch ic = 
           hUpdateAtLabel lch (hUpdateAtLabel att vch och) ic  
           where  lch  = labelLVPair  pch
                  vch  = valueLVPair  pch
                  och  = hLookupByLabel lch ic 



-- | Composition of two rules.
ext ::  Rule sc ip ic' sp' ic'' sp'' -> Rule sc ip ic sp ic' sp'
    -> Rule sc ip ic sp ic'' sp''  
ext f g input = f input . g input


-- {-
-- Monadic Interface 

data Lhs
lhs :: Proxy Lhs
lhs = proxy

class At l m v | l -> v where
  at :: l -> m v

instance (HasField (Proxy (lch,nt)) chi v, MonadReader (Fam chi par) m) 
       => At (Proxy (lch,nt)) m v where
  at lbl = liftM (\(Fam chi _) -> chi # lbl) ask

instance MonadReader (Fam chi par) m
       => At (Proxy Lhs) m par where
  at _ = liftM (\(Fam _ par) -> par) ask

def :: Reader (Fam chi par) a -> ((Fam chi par) -> a)
def = runReader



inhdefM  :: (Defs att nts a ic ic')
         => att-> nts-> Reader (Fam sc ip) a -> Rule sc ip ic sp ic' sp
inhdefM att nts d f  = inhdef att nts (def d f)


syndefM  :: (HExtend (Att att a) sp sp')
         =>  att-> Reader (Fam sc ip) a -> Rule sc ip ic sp ic sp'
syndefM att d f      = syndef att (def d f)


inhmodM  ::  (Mods att nts a ic ic')
         =>  att -> nts -> Reader (Fam sc ip) a -> Rule sc ip ic sp ic' sp
inhmodM att nts d f  = inhmod att nts (def d f)


synmodM  :: (HUpdateAtHNat n (Att att a) sp sp',HFind att ls n,RecordLabels sp ls) 
         => att-> Reader (Fam sc ip) a -> Rule sc ip ic (Record sp) ic (Record sp')
synmodM att v f      = synmod att (def v f)



-- | Field of an aspect. It associates a production 'prd' with a rule 'rule'.
type Prd prd rule = LVPair prd rule

-- | The class 'Com' combines two aspects.
class  Com r r' r'' | r r' -> r''
  where (.+.) :: r -> r' -> r''

instance Com r (Record HNil) r
  where   r .+. _ = r

instance  (  HasLabel lprd r b
          ,  ComSingle b (Prd lprd rprd) r r'''
          ,  Com r''' (Record r') r'')
        => Com  r (Record (HCons (Prd lprd rprd) r')) r''
  where
   r .+. (Record (HCons prd r')) = r''
    where  b       = hasLabel (labelLVPair prd) r
           r'''    = comsingle b prd r
           r''     = r''' .+. (Record r')


class  ComSingle b f r r' | b f r -> r'
  where comsingle :: b -> f -> r -> r'

instance  (  HasField  lprd  r (Rule sc ip ic' sp' ic'' sp'')
          ,  HUpdateAtLabel  lprd (Rule  sc    ip 
                                         ic    sp 
                                         ic''  sp'') 
                             r r')
         => ComSingle   HTrue (Prd lprd (Rule sc ip ic sp ic' sp')) 
                        r r'
   where 
    comsingle _ f r  = hUpdateAtLabel n ((r # n) `ext` v) r
     where  n  = labelLVPair f
            v  = valueLVPair f

instance ComSingle  HFalse f (Record r) (Record (HCons f r))
   where comsingle _ f (Record r) = Record (HCons f r)

-- | Semantic function of a terminal
sem_Lit :: a -> Record HNil -> a
sem_Lit e (Record HNil) = e


-- | The function 'knit' takes the combined rules for a node and the 
--   semantic functions of the children, and builds a
--   function from the inherited attributes of the parent to its
--   synthesized attributes.
knit  ::  (  Kn fc ic sc,  Empties fc ec) 
      =>  Rule sc ip ec (Record HNil) ic sp
          -> fc -> ip -> sp
knit  rule fc ip =  
  let  ec = empties fc 
       (Fam ic sp)   = rule  (Fam sc  ip) 
                             (Fam ec  emptyRecord)
       sc = kn fc ic
  in   sp


 
class Kn fc ic sc  | fc  -> ic sc where  
  kn :: fc -> ic -> sc

instance Kn fc ic sc 
 => Kn (Record fc) (Record ic) (Record sc)  where
  kn (Record fc) (Record ic) = Record $ kn fc ic


instance Kn HNil HNil HNil where
  kn _ _ = hNil

instance Kn fcr icr scr
         => Kn    (HCons (Chi lch (ich->sch))     fcr) 
                  (HCons (Chi lch ich)            icr) 
                  (HCons (Chi lch sch)            scr) 
         where
  kn  ~(HCons pfch fcr) ~(HCons pich icr) = 
    let  scr        = kn fcr icr
         lch        = labelLVPair  pfch
         fch        = valueLVPair  pfch
         ich        = valueLVPair  pich
    in   HCons  (newLVPair lch (fch ich)) scr


class Empties fc ec | fc -> ec where
  empties :: fc -> ec

instance Empties fc ec => Empties (Record fc) (Record ec)
        where empties (Record fc) = Record $ empties fc

instance Empties fcr ecr
         => Empties  (HCons (Chi lch fch)            fcr) 
                     (HCons (Chi lch (Record HNil))  ecr) 
         where
  empties  ~(HCons pch fcr)  = 
    let  ecr     = empties fcr
         lch     = labelLVPair  pch
    in   HCons  (newLVPair lch emptyRecord) ecr 

instance Empties HNil HNil where
  empties _ = hNil


-- | A /copy/ rule copies an inherited attribute from the parent to all its children.
--   The function 'copy' takes the name of an attribute 'att' and 
--   an heterogeneous list of non-terminals 'nts' for which the attribute has to be defined,
--   and generates a copy rule for this.
copy  ::   (Copy att nts vp ic ic', HasField att ip vp) 
      =>   att -> nts -> Rule sc ip ic sp ic' sp
copy att nts (Fam _ ip) = defcp att nts (ip # att)

defcp  ::  Copy att nts vp ic ic' 
       =>  att -> nts -> vp -> (Fam ic sp -> Fam ic' sp)
defcp att nts vp (Fam ic sp)  = 
        Fam (cpychi att nts vp ic) sp

class  Copy att nts vp ic ic' | ic -> ic' where
  cpychi  ::  att -> nts -> vp -> ic -> ic'

instance Copy att nts vp (Record HNil) (Record HNil) where
  cpychi  _ _ _ _ = emptyRecord

instance  ( Copy att nts vp (Record ics) ics'
          , HMember (Proxy t) nts mnts
          , HasLabel att vch mvch 
          , Copy'  mnts mvch att vp 
                   (Chi (Proxy (lch, t)) vch)  
                   pch
          , HExtend pch ics' ic) 
      => Copy  att nts vp 
               (Record (HCons (Chi (Proxy (lch, t)) vch) ics))
               ic
      where 
  cpychi att nts vp (Record (HCons pch ics)) = 
            cpychi' mnts mvch att vp pch .*. ics'
           where  ics'  = cpychi att nts vp (Record ics) 
                  lch   = sndProxy (labelLVPair pch)
                  vch   = valueLVPair pch
                  mnts  = hMember lch nts
                  mvch  = hasLabel att vch

class Copy' mnts mvch att vp pch pch'  | mnts mvch pch -> pch' 
  where
   cpychi'  ::  mnts -> mvch -> att -> vp -> pch -> pch'

instance Copy' HFalse mvch att vp pch pch where 
  cpychi' _ _ _ _ pch = pch

instance Copy' HTrue HTrue att vp pch pch where 
  cpychi' _ _ _ _ pch = pch
 
instance HExtend (Att att vp) vch vch' 
    => Copy' HTrue HFalse att vp  (Chi lch vch) 
                           (Chi lch vch') where
  cpychi' _ _ att vp pch = lch .=. (att .=. vp .*. vch) 
            where  lch  = labelLVPair pch
                   vch  = valueLVPair pch
                   


-- | A /use/ rule declares a synthesized attribute that collects information
--   from some of the children.
--   The function 'use' takes the following arguments: the attribute to be defined, 
--   the list of non-terminals for which the attribute is defined,
--   a monoidal operator which combines the attribute values, 
--   and a unit value to be used in those cases where none of 
--   the children has such an attribute. 
use  ::  (Use att nts a sc, HExtend (Att att a) sp sp') 
     =>  att -> nts -> (a -> a -> a) -> a 
         -> Rule sc ip ic sp ic sp'

use att nts oper unit (Fam sc _) = syndef att val
                    where val = case usechi att nts oper sc of
                                  Just r  -> r
                                  Nothing -> unit 


class Use att nts a sc  where
  usechi :: att -> nts -> (a -> a -> a) -> sc -> Maybe a

instance Use att nts a sc => Use att nts a (Record sc) where
 usechi att nts oper (Record sc) = usechi att nts oper sc

instance Use l nt a HNil where
 usechi _ _ _ _ = Nothing


instance ( HMember (Proxy t) nts mnts
         , Use' mnts att nts a (HCons (LVPair (Proxy (lch, t)) vch) scr))   
       => Use att nts a (HCons (LVPair (Proxy (lch, t)) vch) scr) where
 usechi att nts oper ~sc@(HCons fa _) = usechi' mnts att nts oper sc
                            where mnts = hMember (sndProxy $ labelLVPair fa) nts

class Use' mnts att nts a sc where
 usechi' :: mnts -> att -> nts -> (a -> a -> a) -> sc -> Maybe a

instance (HasField att (Record vch) a, Use att nts a scr)  => 
         Use' HTrue att nts a (HCons (LVPair lch (Record vch)) scr) where
 usechi' _ att nts oper ~(HCons fa scr) = Just $ case usechi att nts oper scr of
                                                   Just r  -> oper a r
                                                   Nothing -> a 
                            where a = valueLVPair fa # att

instance (Use att nts a scr)  => 
         Use' HFalse att nts a (HCons (LVPair lch b) scr) where
 usechi' _ att nts oper ~(HCons _ scr) = usechi att nts oper scr


-- | In the /chain/ rule a value is threaded in a depth-first way through the tree, 
--   being updated every now and then. For this we have chained attributes 
--   (both inherited and synthesized). If a definition for a synthesized attribute 
--   of the parent with this name is missing we look for the right-most child with a 
--   synthesized attribute of this name. If we are missing a definition for one 
--   of the children, we look for the right-most of its left siblings which 
--   can provide such a value, and if we cannot find it there, 
--   we look at the inherited attributes of the father.  
chain  ::  (  Chain att nts val sc ic sp ic' sp' 
           ,  HasField att ip val )
      => att -> nts -> Rule sc ip ic sp ic' sp'
chain att nts (Fam sc ip) = defchn att nts (ip # att) sc


class Chain att nts val sc ic sp ic' sp' | sc ic sp -> ic' sp' where
  defchn :: att -> nts -> val -> sc -> (Fam ic sp -> Fam ic' sp')

instance  (  Chain' msp att nts val sc ic sp ic' sp' 
          ,  HasLabel att sp msp )
      => Chain att nts val sc ic sp ic' sp'
  where
  defchn att nts val sc inp@(Fam _ sp)  = defchn' msp att nts val sc inp 
        where  msp        = hasLabel att sp
               


class Chain' msp att nts val sc ic sp ic' sp' | msp sc ic sp -> ic' sp' where
  defchn' :: msp -> att -> nts -> val -> sc -> Fam ic sp -> Fam ic' sp'


instance   (  ChnChi att nts val sc ic ic' 
           ,  HExtend (Att att val) sp sp' )
      => Chain' HFalse att nts val sc ic sp ic' sp'
  where
  defchn' _ att nts val sc (Fam ic sp)  = 
        let (val',ic') = chnchi att nts val sc ic
        in  Fam ic' (att .=. val' .*. sp)

instance   (  ChnChi att nts val sc ic ic' )
      => Chain' HTrue att nts val sc ic sp ic' sp
  where
  defchn' _ att nts val sc (Fam ic sp)  = 
        let (_,ic') = chnchi att nts val sc ic
        in  Fam ic' sp


class ChnChi att nts val sc ic ic' | sc ic -> ic' where
  chnchi :: att -> nts -> val -> sc -> ic -> (val,ic')


instance ChnChi att nts val (Record HNil) (Record HNil) (Record HNil) where
  chnchi  _ _ val _ _ = (val, emptyRecord)

instance  ( ChnChi att nts val (Record scs) (Record ics) ics'
          , HMember (Proxy t) nts mnts
          , ChnChi'  mnts att val
                     (Chi (Proxy (lch, t)) sch)  
                     (Chi (Proxy (lch, t)) ich)  
                     pch
          , HExtend pch ics' ic) 
      => ChnChi  att nts val 
                 (Record (HCons (Chi (Proxy (lch, t)) sch) scs))
                 (Record (HCons (Chi (Proxy (lch, t)) ich) ics))
                 ic
      where 
  chnchi att nts val (Record (HCons psch scs)) (Record (HCons pich ics)) =  
            let (val'',ics') = chnchi att nts val' (Record scs) (Record ics)  
            in (val'',ich'.*. ics')
           where  (val',ich') = chnchi' mnts att val psch pich  
                  lch   = sndProxy (labelLVPair psch)
                  mnts  = hMember lch nts

class ChnChi' mnts att val sch ich ich'  | mnts sch ich -> ich' 
  where
   chnchi'  ::  mnts -> att -> val -> sch -> ich -> (val,ich')


instance ChnChi' HFalse att val sch ich ich where 
  chnchi' _ _ val _ ich = (val,ich)

instance  ( HasLabel att sch msch 
          , HasLabel att ich mich 
          , ChnChi'' msch mich att val
                     (Chi (Proxy (lch, t)) sch)  
                     (Chi (Proxy (lch, t)) ich)  
                     pch )
      => ChnChi'  HTrue att val
                  (Chi (Proxy (lch, t)) sch)  
                  (Chi (Proxy (lch, t)) ich)  
                  pch
  where
  chnchi' _ att val psch pich = chnchi'' msch mich att val psch pich
           where  sch   = valueLVPair psch
                  ich   = valueLVPair pich
                  msch  = hasLabel att sch
                  mich  = hasLabel att ich


class ChnChi'' msch mich att val sch ich ich'  | msch mich sch ich -> ich' 
  where
   chnchi''  ::  msch -> mich -> att -> val -> sch -> ich -> (val,ich')



instance Fail (IncorrectDef att lch (UndefAtt att)) 
        => ChnChi'' HFalse HTrue att val sch (Chi lch ich) ich' where 
  chnchi'' _ _ _ _ _ _ = undefined

instance Fail (IncorrectDef att lch (UndefAtt att)) 
        => ChnChi'' HFalse HFalse att val sch (Chi lch ich) ich' where 
  chnchi'' _ _ _ _ _ _ = undefined

instance HasField att sch val
        => ChnChi'' HTrue HTrue att val (Chi lch sch) ich ich where 
  chnchi'' _ _ att _ psch ich = (sch # att,ich)
             where sch = valueLVPair psch

instance  (  HasField att sch val
          ,  HExtend (Att att val) ich ich' )
        => ChnChi'' HTrue HFalse att val (Chi lch sch) (Chi lch ich) (Chi lch ich') where 
  chnchi'' _ _ att val psch pich = (sch # att, lch .=. (att .=. val .*. ich))
             where  lch = labelLVPair psch
                    sch = valueLVPair psch
                    ich = valueLVPair pich 

-- | The function 'inhAspect' defines an inherited attribute aspect.
--   It takes as arguments: the name of the attribute 'att', 
--   the list 'nts' of non-terminals where the attribute is defined,
--   the list 'cpys' of productions where the copy rule has to be applied, 
--   and a record 'defs' containing the explicit definitions for some productions.
inhAspect ::  (  AttAspect (FnInh att nts) defs defasp
              ,  DefAspect (FnCpy att nts) cpys cpyasp
              ,  Com cpyasp defasp inhasp)
         => att -> nts -> cpys -> defs -> inhasp
inhAspect att nts cpys defs 
   =     (defAspect  (FnCpy att nts)  cpys)
   .+.   (attAspect  (FnInh att nts)  defs) 


-- | The function 'synAspect' defines a synthesized attribute aspect. 
---  The rule applied is the use rule, 
--   which takes 'op' as the monoidal operator and 'unit' as the unit value. 
synAspect ::  (  AttAspect (FnSyn att) defs defasp
              ,  DefAspect (FnUse att nts op unit) uses useasp
              ,  Com useasp defasp synasp) 
         => att -> nts -> op -> unit -> uses -> defs -> synasp
synAspect att nts op unit uses defs 
   =     (defAspect  (FnUse att nts op unit)    uses)
   .+.   (attAspect  (FnSyn att)                defs)


-- | A chained attribute definition introduces both an inherited 
--   and a synthesized attribute. In this case the pattern to be applied is the chain rule. 
chnAspect ::  (  DefAspect (FnChn att nts) chns chnasp
              ,  AttAspect (FnInh att nts) inhdefs inhasp
              ,  Com chnasp inhasp asp
              ,  AttAspect (FnSyn att) syndefs synasp
              ,  Com asp synasp  asp') 
         => att -> nts -> chns -> inhdefs -> syndefs -> asp'
chnAspect att nts chns inhdefs syndefs 
   =     (defAspect  (FnChn att nts)   chns)
   .+.   (attAspect  (FnInh att nts)   inhdefs)
   .+.   (attAspect  (FnSyn att)       syndefs)



class AttAspect rdef defs rules | rdef defs -> rules 
   where attAspect :: rdef -> defs -> rules

instance  (  AttAspect rdef (Record defs) rules
          ,  Apply rdef def rule  
          ,  HExtend (Prd lprd rule) rules rules' )  
         => AttAspect  rdef 
                       (Record (HCons  (Prd lprd def) 
                                       defs)) 
                       rules' 
  where
   attAspect rdef (Record (HCons def defs)) = 
         let  lprd = (labelLVPair def)
         in   lprd .=. apply rdef (valueLVPair def) 
              .*.  attAspect rdef (Record defs)   


instance AttAspect rdef (Record HNil) (Record HNil) 
  where attAspect _ _ = emptyRecord

{-
data FnSyn att = FnSyn att

instance  (HExtend (LVPair att val) sp sp', TypeCast (Rule sc ip ic sp ic sp') r)
         => Apply  (FnSyn att) (Fam sc ip -> val) r
                    where 
  apply (FnSyn att) f =  typeCast $ syndef att . f 

data FnInh att nt = FnInh att nt

instance  (Defs att nts vals ic ic', TypeCast (Rule sc ip ic sp ic' sp) r)
         => Apply  (FnInh att nts) (Fam sc ip -> vals) r
                    where 
  apply (FnInh att nts) f = typeCast $ inhdef att nts . f 
-}

data FnSyn att = FnSyn att

instance  HExtend (LVPair att val) sp sp'
         => Apply  (FnSyn att) (Fam sc ip -> val) 
                   (Rule sc ip ic sp ic sp') where 
  apply (FnSyn att) f =  syndef att . f 

data FnInh att nt = FnInh att nt

instance  Defs att nts vals ic ic'
         => Apply  (FnInh att nts) (Fam sc ip -> vals) 
                   (Rule sc ip ic sp ic' sp) where 
  apply (FnInh att nts) f = inhdef att nts . f 



class DefAspect deff prds rules | deff prds -> rules 
  where defAspect :: deff -> prds -> rules

instance DefAspect deff HNil (Record HNil) where
  defAspect _ _ = emptyRecord

instance  (  Poly deff deff'
          ,  DefAspect deff prds rules
          ,  HExtend (Prd prd deff') rules rules' )  
         => DefAspect deff (HCons prd prds) rules' where
  defAspect deff (HCons prd prds)  =
              prd .=. poly deff  .*.  defAspect deff prds   


class Poly a b where
  poly :: a -> b

data FnCpy att nts = FnCpy att nts

instance  (  Copy att nts vp ic ic'
          ,  HasField att ip vp
          ,  TypeCast (Rule sc ip ic sp ic' sp) r) 
         => Poly  (FnCpy att nts) r  where 
  poly (FnCpy att nts)  = typeCast $ copy att nts 


data FnUse att nt op unit = FnUse att nt op unit

instance  (  Use att nts a sc
          ,  HExtend (LVPair att a) sp sp'
          ,  TypeCast (Rule sc ip ic sp ic sp') r) 
         => Poly  (FnUse att nts (a -> a -> a) a) r where 
  poly (FnUse att nts op unit)  = typeCast $ use att nts op unit 


data FnChn att nt = FnChn att nt

instance  (  Chain att nts val sc ic sp ic' sp' 
          ,  HasField att ip val 
          ,  TypeCast (Rule sc ip ic sp ic' sp') r) 
      => Poly   (FnChn att nts) r where 
  poly (FnChn att nts) = typeCast $ chain att nts

-}
------ HList

class HBool b => HasLabel l r b | l r -> b
instance HasLabel l r b => HasLabel l (Record r) b
instance (HEq l lp b, HasLabel l r b', HOr b b' b'') 
   => HasLabel l (HCons (LVPair lp vp) r) b''
instance HasLabel l HNil HFalse

hasLabel :: HasLabel l r b => l -> r -> b
hasLabel = undefined

class HUpdateAtLabel l v r r' | l v r -> r' where
  hUpdateAtLabel :: l -> v -> r -> r'

instance  (  RecordLabels r ls, HFind l ls n
          ,  HUpdateAtHNat n (LVPair l v) r r')
      => HUpdateAtLabel l v (Record r) (Record r')
  where
   hUpdateAtLabel l v rec@(Record r) = Record r'
    where
     n    = hFind l (recordLabels rec)
     r'   = hUpdateAtHNat n (newLVPair l v) r



sndProxy :: Proxy (a,b) -> Proxy b
sndProxy _ = undefined

--datatype

data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving Show

--proxy = Proxy


-- Labels (attribute names) for the example
data Att_smin
data Att_ival
data Att_sres

smin = Label :: Label Att_smin
ival = Label :: Label Att_ival
sres = Label :: Label Att_sres

-- Labels for childs
data Ch_tree -- root
data Ch_r    -- node
data Ch_l    -- node
data Ch_i    -- leaf

ch_tree = Label :: Label (Ch_tree, Tree)
ch_r = Label :: Label (Ch_r, Tree)
ch_l = Label :: Label (Ch_l, Tree)
ch_i = Label :: Label (Ch_i, Int)
-- both the name and the type of the child are encoded


data Label a = Label

type SP = Record (HCons (Att (Label Att_smin) Int)
                 (HCons (Att (Label Att_sres) Tree)
                  HNil))

type IL = Record (HCons (Att (Label Att_ival) Int)
                  HNil)

type IR = Record (HCons (Att (Label Att_ival) Int)
                  HNil)

type IC = Record (HCons (Chi (Label (Ch_l,Tree)) IL)
                 (HCons (Chi (Label (Ch_r,Tree)) IR)
                  HNil))

type Output_Node = Fam IC SP


-- Figure 6

leaf_smin (Fam chi par)
  = syndef smin (chi # ch_i)

--leaf_smin
--  :: (HasField (Label (Ch_i, Int)) r val,
--      HExtend (Att (Label Att_smin) val) sp sp') =>
--     Fam r t -> Fam ic sp -> Fam ic sp'
