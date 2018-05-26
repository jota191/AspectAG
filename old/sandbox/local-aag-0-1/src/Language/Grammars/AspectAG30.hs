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


module AspectAG where {-(

              -- * Rules
              Att, Fam(..), Chi, Rule,
 
              emptyRule,

              instdef, locdef,
              inhdef, syndef, 
              inhmod, synmod,
              inhupd, synupd,

              -- ** Monadic

              At(..), lhs, loc, def,
              instdefM, locdefM,
              inhdefM, syndefM, inh, syn,
              inhmodM, synmodM,
              inhupdM, synupdM,

              -- ** Rules Composition
              ext, adapt, rename, mapChildren, fixCst, graft,
              agMacro, (~~>), (==>), (-->), (<.>), ignore, noChild,

              withChild, withChildAtt,

              -- * Aspects
              Prd, (.+.),

              -- * Semantic Functions
              sem_Lit, knit,
              SemType(),

              -- * Common Patterns
              copy, use, chain,

              -- * Defining Aspects
              inhAspect, synAspect, chnAspect,
              attAspect, defAspect, 
              Defs(..),
              -- * Others
              ListNT(..),

              module Data.HList

            ) where -}

import HList hiding ((.+.), hUpdateAtLabel, HUpdateAtLabel)
import FakePrelude
import HListPrelude
import GhcSyntax
import Record hiding (hUpdateAtLabel)
import HArray


import Control.Monad.Reader

-- | Field of an attribution.
type Att att val = LVPair att val

-- | A Family 'Fam' contains a single attribution 'p' for the parent,
--   'l' for local attributes, 'ho' for higer-order attributes and
--   a collection of attributions 'c' for the children. 
data Fam l ho c p = Fam l ho c p


-- | Field of the record of attributions for the children.
type Chi ch atts = LVPair ch atts

-- | The type 'Rule' states that a rule takes as input the local attributes 'lf',
--   the higher-order attributes 'hof', the synthesized attributes 
--   of the children 'sc' and the inherited attributes of the parent 'ip' and returns
--   a function from the output constructed thus far 
--   (local attributes 'l', higher-order attributes 'ho', inherited attributes of the children 
--   'ic' and synthesized attributes of the parent 'sp') to the extended output.
type Rule lf hof sc ip l ho ic sp l' ho' ic' sp' 
          = Fam lf hof sc ip -> Fam l ho ic sp -> Fam l' ho' ic' sp'

-- | An 'emptyRule' does not introduce any new attribute.
emptyRule :: Rule lf hof sc ip l ho ic sp l ho ic sp 
emptyRule =  const id

-- | The function 'instdef' adds the definition of a higher-order attribute.
--   It takes a label 'att' representing the name of the new attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function which 
--   updates the output constructed thus far.
instdef  ::  HExtend (Att att val) ho ho'
         =>  att -> val -> (Fam l ho ic sp -> Fam l ho' ic sp)
instdef  att val (Fam l ho ic sp) = Fam l (att .=. val .*. ho) ic sp

 
-- | The function 'locdef' adds the definition of a local attribute.
--   It takes a label 'att' representing the name of the new attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function which 
--   updates the output constructed thus far.
locdef  ::  HExtend (Att att val) l l'
        =>  att -> val -> (Fam l ho ic sp -> Fam l' ho ic sp)
locdef  att val (Fam l ho ic sp) = Fam (att .=. val .*. l) ho ic sp


-- | The function 'syndef' adds the definition of a synthesized attribute.
--   It takes a label 'att' representing the name of the new attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function which 
--   updates the output constructed thus far.
syndef  ::  HExtend (Att att val) sp sp'
        =>  att -> val -> (Fam l ho ic sp -> Fam l ho ic sp')
syndef  att val (Fam l ho ic sp) = Fam l ho ic (att .=. val .*. sp)


-- | The function 'synmod' modifies the definition of a synthesized attribute.
--   It takes a label 'att' representing the name of the attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function which 
--   updates the output constructed thus far.
synmod  ::  HUpdateAtLabel att val sp sp' 
        =>  att -> val -> Fam l ho ic sp -> Fam l ho ic sp' 
synmod att v (Fam l ho ic sp) = Fam l ho ic (hUpdateAtLabel att v sp) 


synupd  :: (HasField att sp val, HUpdateAtLabel att val' sp sp') 
        => att -> (val -> val') -> Fam l ho ic sp -> Fam l ho ic sp'
synupd att f (Fam l ho ic sp) =  r'
                               where  v  =  f (sp # att)
                                      r' =  Fam l ho ic (hUpdateAtLabel att v sp) 


-- | The function 'inhdef' introduces a new inherited attribute for 
--   a collection of non-terminals.
--   It takes the following parameters:
--     'att': the attribute which is being defined,
--     'nts': the non-terminals with which this attribute is being associated, and
--     'vals': a record labelled with child names and containing values, 
--              describing how to compute the attribute being defined at each 
--              of the applicable child  positions.
--   It builds a function which updates the output constructed thus far.
inhdef  ::  Defs att nts vals ic ic' 
        =>  att -> nts -> vals -> (Fam l ho ic sp -> Fam l ho ic' sp)
inhdef att nts vals (Fam l ho ic sp) = 
        Fam l ho (defs att nts vals ic) sp


-- | The class 'Defs' is defined by induction over the record 'vals' 
--   containing the new definitions. 
--   The function 'defs' inserts each definition into the attribution 
--   of the corresponding child. 
class Defs att nts vals ic ic'  | att nts vals ic -> ic' where
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
       | mch mnts att pv ic -> ic' 
  where singledef :: mch -> mnts -> att -> pv -> ic -> ic'


data IncorrectDef l lch err
data UndefNT t
data UndefProd t
data UndefAtt t

{-
instance Fail (IncorrectDef l lch (UndefNT t)) 
         => SingleDef HTrue HFalse (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singledef = undefined

instance Fail (IncorrectDef l lch (UndefProd (lch,t))) 
         => SingleDef HFalse HTrue (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singledef = undefined
-}

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
        =>  att -> nts -> vals -> (Fam l ho ic sp -> Fam l ho ic' sp)
inhmod att nts vals (Fam l ho ic sp) = 
        Fam l ho (mods att nts vals ic) sp



-- | The class 'Mods' is defined by induction over the record 'vals' 
--   containing the new definitions. 
--   The function 'mods' inserts each definition into the attribution 
--   of the corresponding child. 
class Mods att nts vals ic ic'  | att nts vals ic -> ic' where
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
       | mch mnts att pv ic -> ic' 
  where singlemod :: mch -> mnts -> att -> pv -> ic -> ic'


data IncorrectMod l lch err
{-
instance Fail (IncorrectMod l lch (UndefNT t)) 
         => SingleMod HTrue HFalse (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singlemod = undefined

instance Fail (IncorrectMod l lch (UndefProd (lch,t))) 
         => SingleMod HFalse HTrue (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singlemod = undefined
-}

instance  ( HasField lch ic och
          , HUpdateAtLabel att vch och och'
          , HUpdateAtLabel lch och' ic ic') 
      => SingleMod  HTrue HTrue att (Chi lch vch) ic ic' 
  where singlemod _ _ att pch ic = 
           hUpdateAtLabel lch (hUpdateAtLabel att vch och) ic  
           where  lch  = labelLVPair  pch
                  vch  = valueLVPair  pch
                  och  = hLookupByLabel lch ic 


-------------------------------------------------------------------------------
inhupd  ::  Upds att nts vals ic ic' 
        =>  att -> nts -> vals -> (Fam l ho ic sp -> Fam l ho ic' sp)
inhupd att nts vals (Fam l ho ic sp) = 
        Fam l ho (upds att nts vals ic) sp



class Upds att nts vals ic ic'  | att nts vals ic -> ic' where
  upds :: att -> nts -> vals -> ic -> ic'

instance Upds att nts (Record HNil) ic ic where
  upds _ _ _ ic = ic

instance  ( Upds att nts (Record vs) ic ic'
          , HasLabel (Proxy (lch,t)) ic' mch
          , HMember (Proxy t) nts mnts
          , SingleUpd  mch mnts att 
                  (Chi (Proxy (lch,t)) vch) 
                  ic' ic'' ) 
      => Upds  att nts 
               (Record (HCons  (Chi (Proxy (lch,t)) vch) vs)) 
               ic ic'' 
      where 
  upds att nts ~(Record (HCons pch vs)) ic = 
         singleupd mch mnts att pch ic'  
         where  ic'     = upds att nts (Record vs) ic
                lch     = labelLVPair pch
                mch     = hasLabel lch ic'
                mnts    = hMember (sndProxy lch) nts



class  SingleUpd mch mnts att pv ic ic' 
       | mch mnts att pv ic -> ic' 
  where singleupd :: mch -> mnts -> att -> pv -> ic -> ic'


data IncorrectUpd l lch err
{-
instance Fail (IncorrectUpd l lch (UndefNT t)) 
         => SingleUpd HTrue HFalse (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singleupd = undefined

instance Fail (IncorrectUpd l lch (UndefProd (lch,t))) 
         => SingleUpd HFalse HTrue (Proxy l) (LVPair (Proxy (lch,t)) c) r r' where
 singleupd = undefined

-}
instance  ( HasField lch ic och
          , HasField att och vch
          , HUpdateAtLabel att vch' och och'
          , HUpdateAtLabel lch och' ic ic') 
      => SingleUpd  HTrue HTrue att (Chi lch (vch->vch')) ic ic' 
  where singleupd _ _ att pch ic = 
           hUpdateAtLabel lch (hUpdateAtLabel att vch' och) ic  
           where  lch  = labelLVPair  pch
                  fch  = valueLVPair  pch
                  och  = hLookupByLabel lch ic 
                  vch' = fch (och # att)


-------------------------------------------------------------------------------

-- Rules Composition


-- | Composition of two rules.
ext  ::  Rule lf hof sc ip l' ho' ic' sp' l'' ho'' ic'' sp'' 
     ->  Rule lf hof sc ip l  ho  ic  sp  l'  ho'  ic'  sp'
     ->  Rule lf hof sc ip l  ho  ic  sp  l'' ho'' ic'' sp''  
ext f g input = f input . g input


-- | Adaption of the childen of a rule.
adapt  ::  Rule lf hof sc  ip li hoi ici  spi lo hoo ico  spo 
       ->  (sc' -> sc) -> (ici' -> ici) -> (ico -> ico')
       ->  Rule lf hof sc' ip li hoi ici' spi lo hoo ico' spo

adapt rule fsc fici fico (Fam lf hof sc ip) (Fam li hoi ici spi) =
               let (Fam lo hoo ico spo) = rule (Fam lf hof (fsc sc) ip) (Fam li hoi (fici ici) spi)
               in  (Fam lo hoo (fico ico) spo)

-- | Children renaming.
rename :: (RenRL s sc' sc, RenRL s ici' ici, RenLR s ico ico')  
     => Rule lf hof sc  ip li hoi ici  spi lo hoo ico  spo
     -> s
     -> Rule lf hof sc' ip li hoi ici' spi lo hoo ico' spo
rename asp s = adapt asp (renRL s) (renRL s) (renLR s)  

class RenLR s r r'  | s r -> r' where  
  renLR :: s -> r -> r'

instance RenLR HNil r r where
  renLR _ r = r           


instance ( RenLR s (Record r') (Record r'') 
         , HRLabelSet (HCons (LVPair lr' v) r''), HasField lr r v, H2ProjectByLabels (HCons lr HNil) r t r')
         => RenLR    (HCons (LVPair lr lr')      s) 
                     (Record r) 
                     (Record (HCons (LVPair lr' v) r''))
         where
  renLR (HCons lp s) r =  hExtend (newLVPair lr' v) r''
   where
     lr  = labelLVPair lp
     lr' = valueLVPair lp
     v   = hLookupByLabel lr r
     r'  = hDeleteAtLabel lr r
     r'' = renLR s r'


class RenRL s r r'  | s r -> r' where  
  renRL :: s -> r -> r'

instance RenRL HNil r r where
  renRL _ r = r           

                     
instance ( RenRL s (Record r') (Record r'') 
         , HRLabelSet (HCons (LVPair lr' v) r''), HasField lr r v, H2ProjectByLabels (HCons lr HNil) r t r')
         => RenRL    (HCons (LVPair lr' lr)      s) 
                     (Record r) 
                     (Record (HCons (LVPair lr' v) r''))
         where
  renRL (HCons lp s) r =  hExtend (newLVPair lr' v) r''
   where
     lr' = labelLVPair lp
     lr  = valueLVPair lp
     v   = hLookupByLabel lr r
     r'  = hDeleteAtLabel lr r
     r'' = renRL s r'


-- | Children mapping.
mapChildren :: (MapRL s sc' sc, MapRL s ici' ici, MapLR s ico ico')  
     => Rule lf hof sc  ip li hoi ici  spi lo hoo ico  spo
     -> s
     -> Rule lf hof sc' ip li hoi ici' spi lo hoo ico' spo
mapChildren asp s = adapt asp (mapRL s) (mapRL s) (mapLR s)  

class MapLR s r r'  | s r -> r' where  
  mapLR :: s -> r -> r'


instance ( MapLR l r r') => MapLR (Record l) r r'
         where
  mapLR (Record l) r =  mapLR l r


instance MapLR HNil r (Record HNil) where
  mapLR _ _ = emptyRecord           


instance ( MapLR s (Record r) (Record r'),
           RecordLabels r' ls, HMember lr' ls b, 
           MapLRB b (LVPair lr lr') (Record r) (Record r') (Record r''))
         => MapLR    (HCons (LVPair lr lr')      s) 
                     (Record r)
                     (Record r'')
         where
  mapLR (HCons lp s) r =  mapLRB b lp r r'
   where
     lr' = valueLVPair lp
     r'  = mapLR s r
     b   = hMember lr' (recordLabels r')


class MapLRB b s r r' r''  | b s r r' -> r'' where  
  mapLRB :: b -> s -> r -> r' -> r''

instance ( HRLabelSet (HCons (LVPair lr' v) r'), HasField lr r v)
         => MapLRB   HFalse
                     (LVPair lr lr') 
                     (Record r)
                     (Record r')
                     (Record (HCons (LVPair lr' v) r'))
         where
  mapLRB _ lp r r' =  hExtend (newLVPair lr' v) r'
   where
     lr  = labelLVPair lp
     lr' = valueLVPair lp
     v   = hLookupByLabel lr r

instance MapLRB   HTrue
                     (LVPair lr lr')
                     (Record r)
                     (Record r')
                     (Record r')
         where
  mapLRB _ _ _ r' =  r'



class MapRL s r r'  | s r -> r' where  
  mapRL :: s -> r -> r'

instance ( MapRL l r r') => MapRL (Record l) r r'
         where
  mapRL (Record l) r =  mapRL l r


instance MapRL HNil r (Record HNil) where
  mapRL _ _ = emptyRecord

                     
instance ( MapRL s (Record r) (Record r') 
         , HRLabelSet (HCons (LVPair lr' v) r'), HasField lr r v)
         => MapRL    (HCons (LVPair lr' lr)      s) 
                     (Record r) 
                     (Record (HCons (LVPair lr' v) r'))
         where
  mapRL (HCons lp s) r =  hExtend (newLVPair lr' v) r'
   where
     lr' = labelLVPair lp
     lr  = valueLVPair lp
     v   = hLookupByLabel lr r
     r'  = mapRL s r




-- | Fixing a constant as a child.
fixCst
  :: (RecordLabels r ls,
      HRLabelSet (HCons (LVPair l (Record HNil)) r),
      HExtend (LVPair l v) t2 l',
      HRearrange ls r1 r',
      HLabelSet ls,
      H2ProjectByLabels (HCons l HNil) t10 t11 r1) =>
     (Fam t t1 l' t3
      -> Fam t4 t5 (Record (HCons (LVPair l (Record HNil)) r)) t6
      -> Fam t7 t8 (Record t10) t9)
     -> l
     -> v
     -> Fam t t1 t2 t3
     -> Fam t4 t5 (Record r) t6
     -> Fam t7 t8 (Record r') t9
fixCst rule lch cst (Fam lf hof sc ip) (Fam li hoi ici spi) =
               let  (Fam lo hoo ico spo) = rule (Fam lf hof (lch .=. cst .*. sc) ip) (Fam li hoi (lch .=. emptyRecord .*. ici) spi)
                    ls = recordLabels ici 
                    ico' = hRearrange ls (hDeleteAtLabel lch ico)
               in   (Fam lo hoo ico' spo)

-- | Grafting one tree as a child of the other.
graft ::                (HasField' b e (HCons (LVPair e v2) a3) v,
                         HasField' b e (HCons (LVPair e (Record HNil)) a2) v1,
                         HasField e t2 ip1,
                         RecordLabels t ls2,
                         HEq e e b,
                         HRLabelSet a1,
                         HRLabelSet (HCons (LVPair e (Record HNil)) a2),
                         HRLabelSet a3,
                         HRLabelSet (HCons (LVPair e e) r1),
                         HRLabelSet (HCons (LVPair e v2) a3),
                         HRLabelSet (HCons (LVPair e v) r'),
                         HRLabelSet (HCons (LVPair e v1) r'1),
                         HRLabelSet a2,
                         HRLabelSet a,
                         MapLR r ico1 r3,
                         MapLR (HCons (LVPair e e) r1) ico (Record t2),
                         MapRL r1 (Record (HCons (LVPair e (Record HNil)) a2)) (Record r'1),
                         MapRL r (Record a1) sc,
                         MapRL r (Record a) ici,
                         MapRL r1 (Record (HCons (LVPair e v2) a3)) (Record r'),
                         H2ProjectByLabels ls t1 a1 b2,
                         H2ProjectByLabels ls1 t1 a3 b4,
                         H2ProjectByLabels (HCons e HNil) t2 t3 t4,
                         H2ProjectByLabels ls1 t a2 b3,
                         H2ProjectByLabels ls t a b1,
                         RecordValues r1 ls1,
                         RecordValues r ls,
                         HLeftUnion r3 (Record t4) (Record r2),
                         HRearrange ls2 r2 r'2,
                         HLabelSet ls2) =>
                        Rule
                          lf
                          hof
                          (Record (HCons (LVPair e v) r'))
                          ip
                          li
                          hoi
                          (Record (HCons (LVPair e v1) r'1))
                          spi
                          li1
                          hoi1
                          ico
                          p
                        -> Record r1
                        -> e
                        -> Rule lf hof sc ip1 li1 hoi1 ici (Record HNil) l ho ico1 v2
                        -> Record r
                        -> Fam lf hof (Record t1) ip
                        -> Fam li hoi (Record t) spi
                        -> Fam l ho (Record r'2) p

graft rule1 chs1 lch rule2 chs2  (Fam lf hof sc ip) (Fam l ho ici spi)  =
               let  spi1 = spi
                    spi2 = emptyRecord

                    -- ls1' and ls2 don't need to be disjoint
                    ls1'   = recordValues chs1
                    ls2    = recordValues chs2
                    ici1'  = hProjectByLabels ls1' ici
                    ici2   = hProjectByLabels ls2  ici
                    ici1   = lch .=. emptyRecord .*. ici1' 
                    sc1'   = hProjectByLabels ls1' sc
                    sc2    = hProjectByLabels ls2  sc
                    sc1    = lch .=. spo2 .*. sc1'

                    ip1 = ip
                    ip2 = ico1 # lch

                    (Fam l1 ho1 ico1 spo1) = (mapChildren rule1 (lch .=. lch .*. chs1))  (Fam lf hof sc1 ip1) (Fam l  ho  ici1 spi1) 
                    (Fam l2 ho2 ico2 spo2) = (mapChildren rule2 chs2)                    (Fam lf hof sc2 ip2) (Fam l1 ho1 ici2 spi2)

                    ls = recordLabels ici 
                    ico = hRearrange ls $ hLeftUnion ico2 (hDeleteAtLabel lch ico1)
                    spo = spo1
               in   (Fam l2 ho2 ico spo)


-- | A generalized version of 'graft' that grafts into or maps every children.
agMacro ::              (RecordLabels r ls, HRearrange ls r1 r', HLabelSet ls) =>
                        (  (Fam l1 ho1 c p1 -> Fam l ho c1 p -> Fam t t1 t2 p2)
                        ,  ((l1, ho1, c2, Record r)
                             -> (t, t1, t2, Record HNil, Record HNil)
                             -> (l2, ho2, Record r1, c1, c)))
                        -> Fam l1 ho1 c2 p1
                        -> Fam l ho (Record r) p
                        -> Fam l2 ho2 (Record r') p2
 
agMacro (rule1, chMap) (Fam lf hof sc ip) (Fam l ho ici spi)  =
               let  spi1 = spi
                    ip1  = ip

                    (Fam l1 ho1 ico1 spo1) = rule1  (Fam lf hof sc1 ip1) (Fam l  ho  ici1 spi1) 
                    (l2, ho2, ico, ici1, sc1) = chMap (lf, hof, sc, ici) (l1, ho1, ico1, emptyRecord, emptyRecord) 

                    ls = recordLabels ici 
                    ico' = hRearrange ls ico
                    spo = spo1
               in   (Fam l2 ho2 ico' spo)


infixr 4 ~~>

-- | Child mapping definition, it reads /replaced by the constant/. 
(~~>) ::                (HExtend (LVPair e (Record HNil)) l1 t9,
                         HExtend (LVPair e v) l t10,
                         H2ProjectByLabels (HCons e HNil) t4 t5 t6) =>
                        e
                        -> v
                        -> (t, t1, t2, t3)
                        -> (t7, t8, Record t4, l1, l)
                        -> (t7, t8, Record t6, t9, t10)

lch ~~> cst = \(_, _, _, _) (l1,ho1,ico1,ici1,sc1)  ->
               let  ico1' = hDeleteAtLabel lch ico1
                    ici1' = lch .=. emptyRecord .*. ici1
                    sc1'  = lch .=. cst .*. sc1
               in   (l1, ho1, ico1', ici1',  sc1')




infixr 4 ==>

-- | Child mapping definition, it reads /replaced by/. 
(==>) ::                (HExtend (LVPair l3 v) l2 t14,
                         HExtend (LVPair l3 (Record HNil)) l t13,
                         HasField l3 t7 p,
                         H2ProjectByLabels (HCons l3 HNil) t7 t8 t9,
                         HLeftUnion r (Record t9) t12) =>
                        l3
                        -> (Fam t t1 c p -> Fam l1 ho c1 (Record HNil) -> Fam t4 t5 t6 v,
                            (t, t1, t2, t3)
                            -> (t4, t5, t6, Record HNil, Record HNil)
                            -> (t10, t11, r, c1, c))
                        -> (t, t1, t2, t3)
                        -> (l1, ho, Record t7, l, l2)
                        -> (t10, t11, t12, t13, t14)

lch ==> (rule2, chMap) = \(lf, hof, sc, ici) (l1,ho1,ico1,ici1,sc1)  ->
               let  spi2 = emptyRecord


                    ip2 = ico1 # lch

                    (Fam l2 ho2 ico2 spo2) = rule2  (Fam lf hof sc2 ip2) (Fam l1 ho1 ici2 spi2)
                                       
                    (l2', ho2', ico2', ici2, sc2) = chMap (lf, hof, sc, ici) (l2, ho2, ico2, emptyRecord, emptyRecord) 
  
                    ico1' = hLeftUnion ico2' (hDeleteAtLabel lch ico1)
                    ici1' = lch .=. emptyRecord .*. ici1
                    sc1'  = lch .=. spo2 .*. sc1
               in   (l2', ho2', ico1', ici1', sc1')

 
infixr 4 -->

-- | Child mapping definition, it reads /binds to/.
(-->) ::                (HasField l2 t2 v2, HasField l3 r1 v1, HasField l3 r v,
                         HRLabelSet (HCons (LVPair l3 v2) t6),
                         H2ProjectByLabels (HCons l2 HNil) t2 t3 t4,
                         H2ProjectByLabels (HCons l3 HNil) t4 t5 t6,
                         HExtend (LVPair l2 v1) l1 t9, HExtend (LVPair l2 v) l t10) =>
                        l2
                        -> l3
                        -> (t, t1, r, r1)
                        -> (t7, t8, Record t2, l1, l)
                        -> (t7, t8, Record (HCons (LVPair l3 v2) t6), t9, t10)

lch --> lch2 = \(_, _, sc, ici) (l1,ho1,ico1,ici1,sc1)  ->
               let  ico1' = hRenameLabel' lch lch2 ico1 --(hDeleteAtLabel lch2 ico1)
                    ici1' = lch .=. (ici # lch2) .*. ici1
                    sc1'  = lch .=. (sc # lch2) .*. sc1
               in   (l1, ho1, ico1', ici1',  sc1')


hRenameLabel' ::                (HasField l t v, HRLabelSet (HCons (LVPair l1 v) t4),
                                 H2ProjectByLabels (HCons l1 HNil) t2 t3 t4,
                                 H2ProjectByLabels (HCons l HNil) t t1 t2) =>
                                l -> l1 -> Record t -> Record (HCons (LVPair l1 v) t4)
hRenameLabel' l l' r = r'''
 where
  v    = hLookupByLabel l  r
  r'   = hDeleteAtLabel l  r
  r''  = hDeleteAtLabel l' r'
  r''' = hExtend (newLVPair l' v) r''

infixr 2 <.>


ignore :: HExtend (LVPair lch (Record HNil)) l t6
       => lch
       -> (t, t1, t2, t3) -> (t4, t5, l, t7, t8) -> (t4, t5, t6, t7, t8)
ignore lch2 = \(_, _, sc, ici) (l1,ho1,ico1,ici1,sc1)  ->
               let  ico1' = lch2 .=. emptyRecord .*. ico1
                    ici1' = ici1
                    sc1'  = sc1
               in   (l1, ho1, ico1', ici1',  sc1')


noChild ::  (t, t1, t2, t3) -> (t4, t5, t6, t7, t8) -> (t4, t5, t6, t7, t8)
noChild (_, _, _, _) = id


-- | Composition of children mapping definitions for the function 'macro'.
(<.>)  ::  ((lf,hof,sc,ici) -> (l2,ho2,ico1',ici1',sc1') -> (l3,ho3,ico1'',ici1'',sc1'')) 
       ->  ((lf,hof,sc,ici) -> (l1,ho1,ico1,ici1,sc1) -> (l2,ho2,ico1',ici1',sc1')) 
       ->  (lf,hof,sc,ici) -> (l1,ho1,ico1,ici1,sc1) -> (l3,ho3,ico1'',ici1'',sc1'')
ch1 <.> ch2 = \inp -> (ch1 inp) . (ch2 inp)



withChild ::  HasField lch sc v 
          =>  lch -> (v -> Rule lf hof sc ip l ho ic sp l' ho' ic' sp')
          ->  Rule lf hof sc ip l ho ic sp l' ho' ic' sp'
withChild lch rule (Fam lf hof sc ip) (Fam li hoi ici spi) =
                   rule (sc # lch) (Fam lf hof sc ip) (Fam li hoi ici spi)


withChildAtt ::  (HasField lch sc r, HasField att r v) 
             =>  lch -> att -> (v -> Rule lf hof sc ip l ho ic sp l' ho' ic' sp')
             ->  Rule lf hof sc ip l ho ic sp l' ho' ic' sp'
withChildAtt lch att rule (Fam lf hof sc ip) (Fam li hoi ici spi) =
                   rule ((sc # lch) # att) (Fam lf hof sc ip) (Fam li hoi ici spi)


-- Monadic Interface 

data Lhs
lhs :: Proxy Lhs
lhs = proxy 

data Loc
loc :: Proxy Loc
loc = proxy 

class At l m v | l m -> v where
  at :: l -> m v

instance (HasField (Proxy (lch,nt)) chi v, MonadReader (Fam l ho chi par) m) 
       => At (Proxy (lch,nt)) m v where
  at lbl = liftM (\(Fam _ _ chi _) -> chi # lbl) ask


instance MonadReader (Fam l ho chi par) m
       => At (Proxy Lhs) m par where
  at _ = liftM (\(Fam _ _ _ par) -> par) ask

instance MonadReader (Fam l ho chi par) m
       => At (Proxy Loc) m l where
  at _ = liftM (\(Fam l _ _ _) -> l) ask


-- for the static case
instance (MonadReader (Fam l ho chi par) m) 
       => At (chi -> v) m v where
  at lbl = liftM (\(Fam _ _ chi _) -> lbl chi) ask


def :: Reader (Fam l ho chi par) a -> ((Fam l ho chi par) -> a)
def = runReader



instdefM  ::  (HExtend (Att att a) ho ho') 
          =>  att -> Reader (Fam lf hof sc ip) a 
          ->  Rule lf hof sc ip l ho ic sp l ho' ic sp
instdefM att d inp  = instdef att (def d inp) 

locdefM  ::  (HExtend (Att att a) l l') 
         =>  att -> Reader (Fam lf hof sc ip) a 
         ->  Rule lf hof sc ip l ho ic sp l' ho ic sp
locdefM att d inp  = locdef att (def d inp) 

inhdefM  ::  (Defs att nts a ic ic') 
         =>  att-> nts-> Reader (Fam lf hof sc ip) a 
         ->  Rule lf hof sc ip l ho ic sp l ho ic' sp
inhdefM att nts d inp  = inhdef att nts (def d inp)


inh  ::  (Defs att nts a ic ic') 
     =>  att-> nts-> Reader (Fam lf hof sc ip) a 
     ->  Rule lf hof sc ip l ho ic sp l ho ic' sp
inh = inhdefM

syndefM  ::  (HExtend (Att att a) sp sp') 
         =>  att-> Reader (Fam lf hof sc ip) a 
         ->  Rule lf hof sc ip l ho ic sp l ho ic sp'
syndefM att d inp  = syndef att (def d inp) 


syn  ::  (HExtend (Att att a) sp sp') 
     =>  att-> Reader (Fam lf hof sc ip) a 
     ->  Rule lf hof sc ip l ho ic sp l ho ic sp'
syn = syndefM

inhmodM  ::  (Mods att nts a ic ic') 
         =>  att -> nts -> Reader (Fam lf hof sc ip) a 
         ->  Rule lf hof sc ip l ho ic sp l ho ic' sp
inhmodM att nts d inp  = inhmod att nts (def d inp) 

inhupdM att nts d inp  = inhupd att nts (def d inp) 



synmodM  ::  (HUpdateAtHNat n (Att att a) sp sp',HFind att ls n,RecordLabels sp ls) 
         =>  att-> Reader (Fam lf hof sc ip) a 
         ->  Rule lf hof sc ip l ho ic (Record sp) l ho ic (Record sp') 
synmodM att d inp    = synmod att (def d inp) 

synupdM att d inp    = synupd att (def d inp) 


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

instance  (  HasField  lprd  r (Rule lf hof sc ip l' ho' ic' sp' l'' ho'' ic'' sp'')
          ,  HUpdateAtLabel  lprd (Rule  lf   hof  sc    ip 
                                         l    ho   ic    sp 
                                         l''  ho'' ic''  sp'') 
                             r r')
         => ComSingle   HTrue (Prd lprd (Rule lf hof sc ip l ho ic sp l' ho' ic' sp')) 
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
knit  ::  (HLeftUnion fc ho fc', Kn fc' ic sc,  Empties fc' ec) 
      =>  Rule l ho sc ip (Record HNil) (Record HNil) ec (Record HNil) l ho ic sp
          -> fc -> ip -> sp
knit  rule fc ip =  
  let  fc' = hLeftUnion fc ho 
       ec = empties fc'

       (Fam l ho ic sp)   = rule  (Fam l            ho           sc  ip) 
                                  (Fam emptyRecord  emptyRecord  ec  emptyRecord)
       sc = kn fc' ic
  in   sp


class Kn fc ic sc | fc -> ic sc where  
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


class SemType t nt | t -> nt

class ListNT nt tHd tTl where
 ch_hd :: Proxy (tHd, nt)
 ch_tl :: Proxy (tTl, [nt])

 ch_hd = proxy
 ch_tl = proxy



-- | A /copy/ rule copies an inherited attribute from the parent to all its children.
--   The function 'copy' takes the name of an attribute 'att' and 
--   an heterogeneous list of non-terminals 'nts' for which the attribute has to be defined,
--   and generates a copy rule for this.
copy  ::   (Copy att nts vp ic ic', HasField att ip vp) 
      =>   att -> nts -> Rule lf hof sc ip l ho ic sp l ho ic' sp
copy att nts (Fam _ _ _ ip) = defcp att nts (ip # att)

defcp  ::  Copy att nts vp ic ic' 
       =>  att -> nts -> vp -> (Fam l ho ic sp -> Fam l ho ic' sp)
defcp att nts vp (Fam l ho ic sp)  = 
        Fam l ho (cpychi att nts vp ic) sp

class  Copy att nts vp ic ic' | att nts vp ic -> ic' where
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

class Copy' mnts mvch att vp pch pch'  | mnts mvch att vp pch -> pch' 
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
         -> Rule lf hof sc ip l ho ic sp l ho ic sp'

use att nts oper unit (Fam _ _ sc _) = syndef att val
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

instance (HasField att vch a, HasField att (Record vch) a, Use att nts a scr)  => 
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
chain  ::  (  Chain att nts val sc l ho ic sp ic' sp' 
           ,  HasField att ip val )
      => att -> nts -> Rule lf hof sc ip l ho ic sp l ho ic' sp'
chain att nts (Fam _ _ sc ip) = defchn att nts (ip # att) sc


class Chain att nts val sc l ho ic sp ic' sp' | att nts val sc ic sp -> ic' sp' where
  defchn :: att -> nts -> val -> sc -> (Fam l ho ic sp -> Fam l ho ic' sp')

instance  (  Chain' msp att nts val sc l ho ic sp ic' sp' 
          ,  HasLabel att sp msp )
      => Chain att nts val sc l ho ic sp ic' sp'
  where
  defchn att nts val sc inp@(Fam _ _ _ sp)  = defchn' msp att nts val sc inp 
        where   msp        = hasLabel att sp
               


class Chain' msp att nts val sc l ho  ic sp ic' sp' | msp att nts val sc ic sp -> ic' sp' where
  defchn' :: msp -> att -> nts -> val -> sc -> Fam l ho ic sp -> Fam l ho ic' sp'


instance   (  ChnChi att nts val sc ic ic' 
           ,  HExtend (Att att val) sp sp' )
      => Chain' HFalse att nts val sc l ho ic sp ic' sp'
  where
  defchn' _ att nts val sc (Fam l ho ic sp)  = 
        let (val',ic') = chnchi att nts val sc ic
        in  Fam l ho ic' (att .=. val' .*. sp)

instance   (  ChnChi att nts val sc ic ic' )
      => Chain' HTrue att nts val sc l ho ic sp ic' sp
  where
  defchn' _ att nts val sc (Fam l ho ic sp)  = 
        let (_,ic') = chnchi att nts val sc ic
        in  Fam l ho ic' sp


class ChnChi att nts val sc ic ic' | att nts val sc ic -> ic' where
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

class ChnChi' mnts att val sch ich ich'  | mnts att val sch ich -> ich' 
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


class ChnChi'' msch mich att val sch ich ich'  | msch mich att val sch ich -> ich' 
  where
   chnchi''  ::  msch -> mich -> att -> val -> sch -> ich -> (val,ich')


{-
instance Fail (IncorrectDef att lch (UndefAtt att)) 
        => ChnChi'' HFalse HTrue att val sch (Chi lch ich) ich' where 
  chnchi'' _ _ _ _ _ _ = undefined

instance Fail (IncorrectDef att lch (UndefAtt att)) 
        => ChnChi'' HFalse HFalse att val sch (Chi lch ich) ich' where 
  chnchi'' _ _ _ _ _ _ = undefined
-}
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
{-
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
-}
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



--------------------------------------------
{-
data FnSyn att = FnSyn att

instance  HExtend (LVPair att val) sp sp'
         => Apply  (FnSyn att) (Fam lf hof sc ip -> val) 
                   (Rule lf hof sc ip l ho ic sp l ho ic sp') where 
  apply (FnSyn att) f =  syndef att . f 

data FnInh att nt = FnInh att nt

instance  Defs att nts vals ic ic'
         => Apply  (FnInh att nts) (Fam lf hof sc ip -> vals) 
                   (Rule lf hof sc ip l ho ic sp l ho ic' sp) where 
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
          ,  TypeCast (Rule lf hof sc ip l ho ic sp l ho ic' sp) r) 
         => Poly  (FnCpy att nts) r  where 
  poly (FnCpy att nts)  = typeCast $ copy att nts 


data FnUse att nt op unit = FnUse att nt op unit

instance  (  Use att nts a sc
          ,  HExtend (LVPair att a) sp sp'
          ,  TypeCast (Rule lf hof sc ip l ho ic sp l ho ic sp') r) 
         => Poly  (FnUse att nts (a -> a -> a) a) r where 
  poly (FnUse att nts op unit)  = typeCast $ use att nts op unit 


data FnChn att nt = FnChn att nt

instance  (  Chain att nts val sc l ho ic sp ic' sp'
          ,  HasLabel att sp msp
          ,  Chain' msp att nts val sc l ho ic sp ic' sp' 
          ,  HasField att ip val 
          ,  TypeCast (Rule lf hof sc ip l ho ic sp l ho ic' sp') r) 
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

