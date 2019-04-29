
{-|

Module      : Language.Grammars.AspectAG
Description : Main module, First-class attribute grammars
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX


The original version of the library is documented in the paper:
/Attribute Grammars Fly First-Class.
How to do aspect oriented programming in Haskell/

This was implemented from scratch using the improvements on GHC on the last
10 years, allowing a broad set of techniques for doing type level programming.

-}

{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
module Language.Grammars.AspectAG (
              module Language.Grammars.AspectAG,
              module Language.Grammars.AspectAG.Attribute,
              module Language.Grammars.AspectAG.Attribution,
              module Language.Grammars.AspectAG.ChildAtts,
              module Language.Grammars.AspectAG.Record,
              module Language.Grammars.AspectAG.TagUtils,
              module Language.Grammars.AspectAG.HList,
          --  module Language.Grammars.AspectAG.Notation,
              module Language.Grammars.AspectAG.GenRecord,
              module Language.Grammars.AspectAG.TypeError,
              module Language.Grammars.AspectAG.TPrelude
            ) where


import Language.Grammars.AspectAG.HList
import Language.Grammars.AspectAG.Attribution
import Language.Grammars.AspectAG.Record
import Language.Grammars.AspectAG.Attribute
import Data.Kind
import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.TPrelude
import Data.Proxy
import Language.Grammars.AspectAG.ChildAtts
import Language.Grammars.AspectAG.TagUtils
--import Language.Grammars.AspectAG.Notation
import Language.Grammars.AspectAG.GenRecord
import GHC.TypeLits
import Language.Grammars.AspectAG.TypeError
import Data.Maybe
import GHC.Types
import Data.Type.Equality

-- | In each node of the grammar, the "Fam" contains a single attribution
--for the parent, and a collection (Record) of attributions for the children:
data Fam (c::[((k, Type),[(k,Type)])]) (p :: [(k,Type)]) :: Type where
  Fam :: ChAttsRec c -> Attribution p -> Fam c p


-- | desctructors
chi :: Fam c p -> ChAttsRec c
chi (Fam chi _) = chi

par :: Fam c p -> Attribution p
par (Fam _ par) = par

-- | Rules, aka definition of attribution computations
--Rules are defined as a mapping from an input family to an output family,
--the added arity is for make them composable

type Rule (sc  :: [((k,Type), [(k, Type)])])
          (ip  :: [(k,       Type)])
          (ic  :: [((k,Type), [(k, Type)])])
          (sp  :: [(k,       Type)])
          (ic' :: [((k,Type), [(k, Type)])])
          (sp' :: [(k,       Type)])
  = Fam sc ip -> Fam ic sp -> Fam ic' sp'

-- | Composition of rules
ext :: Rule sc ip ic sp ic' sp'
  -> (Fam sc ip -> a0 -> Fam ic sp)
  -> (Fam sc ip -> a0 -> Fam ic' sp')
(f `ext` g) input = f input . g input


-- | Type level getters for Rules
type family Syn1 (rule :: Type) :: [((k,Type), [(k, Type)])] where
  Syn1 (Rule sc ip ic  sp  ic'' sp'') = sc
type family Inh1 (rule :: Type) :: [(k, Type)] where
  Inh1 (Rule sc ip ic  sp  ic'' sp'') = ip
type family Syn2 (rule :: Type) :: [((k,Type), [(k, Type)])] where
  Syn2 (Rule sc ip ic  sp  ic'' sp'') = ic
type family Inh2 (rule :: Type) :: [(k, Type)] where
  Inh2 (Rule sc ip ic  sp  ic'' sp'') = sp
type family Syn3 (rule :: Type) :: [((k,Type), [(k, Type)])] where
  Syn3 (Rule sc ip ic  sp  ic'' sp'') = ic''
type family Inh3 (rule :: Type) :: [(k, Type)] where
  Inh3 (Rule sc ip ic  sp  ic'' sp'') = sp''



-- |The function 'syndef' adds the definition of a synthesized attribute.
--It takes a label 'att' representing the name of the new attribute, 
--a value 'val' to be assigned to this attribute, and it builds a function which 
--updates the output constructed thus far.
syndef  :: (LabelSet ( '(att,val) ': sp), Ctx att) =>
    Label att -> val -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
syndef latt val (Fam ic sp) = Fam ic (latt =. val *. sp)

-- | The function 'synmod' modifies the definition of a synthesized attribute.
--   It takes a label 'att' representing the name of the attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function
--   which  updates the output constructed thus far.
synmod  ::  ( UpdateAtLabelAttF att val sp
            , UpdateAtLabelAttFR att val sp ~ sp')
  =>  Label att -> val -> Fam ic sp -> Fam ic sp'
synmod att v (Fam ic sp) = Fam ic (updateAtLabelAttF att v sp)

------------------------------------------------------------------------------

-- | The function 'inhdef' introduces a new inherited attribute for 
--   a collection of non-terminals.
--   It takes the following parameters:
--     'att': the attribute which is being defined,
--     'nts': the non-terminals with which this attribute is being associated
--     'vals': a record labelled with child names and containing values, 
--              describing how to compute the attribute being defined at each 
--              of the applicable child  positions.
--   It builds a function which updates the output constructed thus far.
inhdef :: Defs att nts vals ic
  => Label att -> HList nts -> Record vals
  -> (Fam ic sp -> Fam (DefsR att nts vals ic) sp)
inhdef att nts vals (Fam ic sp) = Fam (defs att nts vals ic) sp


-- | singledef is an auxiliar function to implement Defs.
--   it inserts a definition into the attribution of the corresponding child
-- mch  ~ memnership of chld
-- mnts ~ membership of nonterminals

class SingleDef (mch::Bool)(mnts::Bool) att pv (ic ::[((k,Type),[(k,Type)])]) where
  type SingleDefR mch mnts att pv ic :: [((k,Type),[(k,Type)])]
  singledef :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
                -> ChAttsRec (SingleDefR mch mnts att pv ic)

instance ( HasChildF lch ic
         , och ~ LookupByChildFR lch ic
         , UpdateAtChildF lch ( '(att,vch) ': och) ic
         , LabelSet ( '(att, vch) ': och)) =>
  SingleDef 'True 'True att (Tagged lch vch) ic where
  type SingleDefR 'True 'True att (Tagged lch vch) ic
    = UpdateAtChildFR lch ( '(att,vch) ': (LookupByChildFR lch ic)) ic
  singledef _ _ att pch ic
    = updateAtChildF (Label :: Label lch) ( att =. vch *. och) ic
    where lch = labelTChAtt pch
          vch = unTaggedChAtt pch
          och = lookupByChildF lch ic

-- | Error instance, undefined Non Terminal
type UndefinedNonTerminal t = () -- TODO

instance (TypeError (Text "TypeError: Undefined non terminal."
                :$$: Text "In some definition of an INHERITED attribute "
                :$$: Text "there is a children associated to a non-terminal: "
                :<>: ShowType t
                :$$: Text "for which the attribute is not being declared."),
          pv ~ Tagged (lch, t) vch
          )
  => SingleDef 'True 'False att pv ic where
  type SingleDefR 'True 'False att pv ic = '[]
  singledef = undefined


-- | Error instance, undefined Non Terminal/Child
type UndefinedNonTerminalCh t = () -- TODO
instance (TypeError (Text "undefined Non Terminal/Child" :$$:
                     Text "Non-terminal named: " :<>: ShowType t :$$:
                     Text "Child named: " :<>: ShowType lch :<>:
                     Text " related to that terminal")
         , pv ~ Tagged (lch, t) vch
         )
  => SingleDef 'False 'False att pv ic where
  type SingleDefR 'False 'False att pv ic = '[]
  singledef = undefined



-- | The class 'Defs' is defined by induction over the record 'vals' 
--   containing the new definitions. 
--   The function 'defs' inserts each definition into the attribution 
--   of the corresponding child.

class Defs att (nts :: [Type])
            (vals :: [((k,Type),Type)]) (ic :: [((k,Type),[(k,Type)])]) where
  type DefsR att nts vals ic :: [((k,Type),[(k,Type)])]
  defs :: Label att -> HList nts -> Record vals -> ChAttsRec ic
       -> ChAttsRec (DefsR att nts vals ic)

instance Defs att nts '[] ic where
  type DefsR att nts '[] ic = ic
  defs _ _ _ ic = ic

instance ( Defs att nts vs ic
         , ic' ~ DefsR att nts vs ic
         , HMember' t nts
         , HMemberRes' t nts ~ mnts
         , HasLabelChildAttsRes '(lch,t) ic' ~ mch
         , HasLabelChildAtts '(lch,t) ic'
         , SingleDef mch mnts att (Tagged '(lch,t) vch) ic') => 
  Defs att nts ( '( '(lch,t), vch) ': vs) ic where
  type DefsR att nts ( '( '(lch,t), vch) ': vs) ic
    = SingleDefR (HasLabelChildAttsRes '(lch,t) (DefsR att nts vs ic))
                 (HMemberRes' t nts)
                 att
                 (Tagged '(lch,t) vch)
                 (DefsR att nts vs ic)
  defs att nts (ConsR pch vs) ic = singledef mch mnts att pch ic' 
      where ic'  = defs att nts vs ic
            lch  = labelLVPair pch
            mch  = hasLabelChildAtts lch ic'
            mnts = hMember' (sndLabel lch) nts

-- * Aspects: Aspects are record that have a rule for each production:
-- | aspects are actually records
type Aspect = Record


-- | Let a Type for the fields:
type Prd prd rule = Tagged prd rule

labelPrd (Tagged v :: Tagged l v) = Label :: Label l 
rulePrd (Tagged v)= v


-- | Lets define the combination of aspects. When labels are only present once,
--  the new aspect has a copy of the field. In the other hand, when a label is
--  repeated, rules are combined with the function ext.
class Com (r :: [(k,Type)]) (s :: [(k, Type)]) where
  type (.++.) r s :: [(k,Type)]
  (.+.) :: Aspect r -> Aspect s -> Aspect (r .++. s)


-- | ComSingle inserts one Rule in an aspect
-- The boolean parameter is True if prd is a label in the record.
class ComSingle (b::Bool) (prd :: k) (rule :: Type) (r :: [(k,Type)]) where
  type ComSingleR b prd rule r :: [(k, Type)]
  comSingle :: Proxy b -> Prd prd rule -> Aspect r
            -> Aspect (ComSingleR b prd rule r)


-- | When there is no production with the name prd, the map is simply extended
instance ( LabelSet ('(prd, rule) ': r)) => 
  ComSingle 'False prd rule r where
  type ComSingleR 'False prd rule r = '(prd, rule) ': r
  comSingle _ prd asp = prd .*. asp

-- | When the production is already defined, the new
-- rule must be combined with the previous one
instance ( UpdateAtLabelRecF prd (Rule sc ip ic  sp  ic'' sp'') r
         , HasFieldRec prd r
         , LookupByLabelRec prd r ~ (Rule sc ip ic' sp' ic'' sp'')
         , ic'' ~ (Syn3 (LookupByLabelRec prd r))
         , sp'' ~ (Inh3 (LookupByLabelRec prd r))
         ) =>
  ComSingle 'True prd (Rule sc ip ic  sp  ic'  sp') r where
  type ComSingleR 'True prd (Rule sc ip ic  sp  ic'  sp') r
    = UpdateAtLabelRecFR prd (Rule sc ip ic sp (Syn3 (LookupByLabelRec prd r))
                                               (Inh3 (LookupByLabelRec prd r))) r
  comSingle _ f r = updateAtLabelRecF l (oldR `ext` newR) r 
    where l    = labelPrd f
          oldR = lookupByLabelRec l r
          newR = rulePrd f


-- | Unicode pretty operator
(⊕) :: (Com r s) => Aspect r -> Aspect s -> Aspect (r .++. s)
(⊕) = (.+.)


-- | The proper Com, by induction over the second Aspect.

-- | The empty record is a neutral element by right
instance Com r '[] where
  type r .++. '[] = r
  r .+. _ = r

-- | For the recursive step, take the head of the second argument,
-- use comsingle on the first parameter, call (.+.) with the result
-- and the tail
instance ( Com (ComSingleR (HasLabelRecRes prd r) prd rule r)  r'
         , HasLabelRecRes prd r ~ b
         , HasLabelRec prd r
         , ComSingle b prd rule r)
  => Com r ( '(prd, rule) ': r') where
     type r .++. ( '(prd, rule) ': r')
       = (ComSingleR (HasLabelRecRes prd r) prd rule r) .++. r'
     r .+. (pr `ConsR` r') = let b   = hasLabelRec (labelPrd pr) r
                                 r'''= comSingle b pr r
                                 r'' = r''' .+. r'
                             in  r''



-- | The function 'knit' takes the combined rules for a node and the 
--   semantic functions of the children, and builds a
--   function from the inherited attributes of the parent to its
--   synthesized attributes.

knit :: ( Empties fc
        , Kn fc ) =>
  Rule (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp
     -> Record fc -> Attribution ip -> Attribution sp
knit rule fc ip
  = let ec          = empties fc
        (Fam ic sp) = rule (Fam sc ip) (Fam ec emptyAtt)
        sc          = kn fc ic
    in  sp


-- ------------------------------------------------------------------------------

class Empties (fc :: [((k, Type),Type)]) where
  type EmptiesR fc :: [((k, Type), [(k, Type)])] -- KnownBug, k = k' from here
  empties :: Record fc -> ChAttsRec (EmptiesR fc)

instance Empties '[] where
  type EmptiesR '[] = '[]
  empties EmptyR = emptyCh


-- instance (( Empties fcr
--          , LabelSet ( '( '(lch, t), '[]) ': EmptiesR fcr)) )
--   => Empties ( '( '(lch, t), Type) ': fcr) where
--   type EmptiesR ( '( '(lch, t), Type) ': fcr)
--      = '( '(lch, t), '[]) ': EmptiesR fcr
--   empties (ConsR pch fcr)
--     = let lch = labelTChAtt pch
--       in  (lch .= emptyAtt) .* (empties fcr)

instance (( Empties fcr
         , LabelSet ( '( '(lch, t), '[]) ': EmptiesR fcr)) )
  => Empties ( '( '(lch, t), Attribution e -> Attribution a) ': fcr) where
  type EmptiesR ( '( '(lch, t), Attribution e -> Attribution a) ': fcr)
     = '( '(lch, t), '[]) ': EmptiesR fcr
  empties (ConsR pch fcr)
    = let lch = labelTChAtt pch
      in  (lch .= emptyAtt) .* (empties fcr)

-- the Kn class

class Kn (fcr :: [((k, Type), Type)]) where
  type ICh fcr :: [((k, Type), [(k, Type)])]
  type SCh fcr :: [((k, Type), [(k, Type)])]
  kn :: Record fcr -> ChAttsRec (ICh fcr) -> ChAttsRec (SCh fcr)

instance Kn '[] where
  type ICh '[] = '[]
  type SCh '[] = '[] 
  kn _ _ = emptyCh

instance ( Kn fc
         , LabelSet ('(lch, sch) : SCh fc)
         , LabelSet ('(lch, ich) : ICh fc)) => 
  Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) where
  type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , ich) ': ICh fc
  type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , sch) ': SCh fc
  kn (ConsR pfch fcr) (ConsR pich icr)
   = let scr = kn fcr icr
         lch = labelTChAtt pfch
         fch = unTagged pfch
         ich = unTaggedChAttr pich
     in ConsR (TaggedChAttr lch (fch ich)) scr


-----------------------------------------------------------------------------

-- | A /use/ rule declares a synthesized attribute that collects information
--   from some of the children.
--   The function 'use' takes the following arguments:
--   - att:  the attribute to be defined, 
--   - nts:  the list of non-terminals for which the attribute is defined,
--   - op :  a monoidal operator which combines the attribute values, 
--   - unit: and a unit value to be used in those cases where none of 
--           the children has such an attribute. 

use :: (Use att nts a sc, LabelSet ( '(att, a) ': sp)) =>
    Label att -> HList nts -> (a -> a -> a) -> a 
           -> Rule sc ip ic sp ic ( '(att, a) ': sp)
use att nts op unit (Fam sc _)
  = let res = usechi att nts op sc
    in  syndef att $ maybe unit id res

-- | The class to implement the dependent function /usechi/

class Use (att :: k) (nts :: [Type]) (a :: Type) sc -- TODO:
 where
  usechi :: Label att -> HList nts -> (a -> a -> a) -> ChAttsRec sc
         -> Maybe a


instance Use att nts a '[] where
  usechi _ _ _ _ = Nothing

instance ( HMember' t nts
         , HMemberRes' t nts ~ mnts
         , Use' mnts att nts a ( '( '(lch, t ), attr) ': scr))
  => Use att nts a ( '( '(lch, t ), attr) ': scr) where
  usechi att nts op (ConsR lattr scr)
    = let k = ()
         --  mnts = hMember' (sndLabel (labelChAttr lattr)) nts
      in  usechi' (Proxy @ mnts) att nts op (ConsR lattr scr)
    
-- | /usechi'/ to pattern match on /mnts/
class Use' (mnts :: Bool) (att :: k) (nts :: [Type]) (a :: Type) sc
 where
  usechi' :: Proxy mnts -> Label att -> HList nts -> (a -> a -> a)
          -> ChAttsRec sc -> Maybe a

-- instance ( LabelSet ( '(lch, b) ': scr) -- FIXME: needed since we use ConsR 
--          , Use att nts a scr )
--   => Use' False att nts a ( '(lch, b) ': scr) where
--   usechi' _ att nts a (ConsCh _ scr) = usechi att nts a scr

instance Use att nts a scr
  => Use' False att nts a ( '(lch, attr) ': scr) where
  usechi' _ att nts op scr = usechi att nts op $ tailRec scr

instance ( HasFieldAttF att attr
         , LookupByLabelAttFR att attr ~ a
         , Use att nts a scr
         , LabelSet ( '( '(lch,t), attr) ': scr)) -- FIXME: pattern syn
  => Use' True att nts a ( '( '(lch,t), attr) ': scr) where
  usechi' _ att nts op (ConsCh lattr scr)
    = let attr = unTaggedChAttr lattr
          val  = attr #. att
      in  Just $ maybe val (op val) $ usechi att nts op scr


--------------------------------------------------------------------------------

-- | A /copy/ rule copies an inherited attribute from the parent to all its
-- children.
-- The function 'copy' takes
-- - 'att' : the name of an attribute 
-- - 'nts' : an heterogeneous list of non-terminals for which the attribute
--           has to be defined,
-- and generates a copy rule for this.


copy  :: ( Copy att nts (LookupByLabelAttFR att ip) ic
         , HasFieldAttF att ip) 
  =>   Label att -> HList nts
  -> Rule sc ip ic sp (CopyR att nts (LookupByLabelAttFR att ip) ic) sp
copy att nts (Fam _ ip) = defcp att nts (ip #. att)

defcp  ::  Copy att nts vp ic
       =>  Label att -> HList nts -> vp
       -> Fam ic sp -> Fam (CopyR att nts vp ic) sp
defcp att nts vp (Fam ic sp)
  = Fam (cpychi att nts vp ic) sp



-- | inserts the attribute in every children
class Copy (att :: k)
           (nts :: [Type])
           (vp  :: Type)
           (ic  :: [((k,Type),[(k,Type)])]) where
  type CopyR att nts vp ic :: [((k,Type), [(k,Type)])]
  cpychi :: Label att
         -> HList nts
         -> vp
         -> ChAttsRec ic
         -> ChAttsRec (CopyR att nts vp ic)

instance Copy att nts vp '[] where
  type CopyR att nts vp '[] = '[]
  cpychi _ _ _ _ = EmptyCh

instance ( Copy att nts vp ics
         , Copy' mnts mvch att vp '(lch,t) vch
         , mnts ~ HMemberRes' t nts
         , HMember' t nts
         , HasLabelAtt att vch
         , mvch ~ HasLabelAttR att vch
         , LabelSet ( '( '(lch, t), vch) : ics)
         , (LabelSet( '( '(lch, t), CopyR' mnts mvch att vp '(lch, t) vch)
                     ': CopyR att nts vp ics))
         )
  => Copy att nts vp ( '( '(lch,t), vch) ': ics) where
  type CopyR att nts vp ( '( '(lch,t), vch) ': ics)
    =  '( '(lch, t) ,CopyR' (HMemberRes' t nts)
                (HasLabelAttR att vch) att vp '(lch,t) vch)
       ': CopyR att nts vp ics
  cpychi att nts vp (ConsCh tgchatt ics)
    = let ics'  = cpychi att nts vp ics
          lcht  = labelChAttr tgchatt
          vch   = unTaggedChAttr tgchatt
          mnts  = hMember' (sndLabel lcht) nts
          mvch  = hasLabelAtt att vch
          attr  = cpychi' mnts mvch att vp lcht vch
      in  (lcht .= attr) .* ics'


class Copy' (mnts :: Bool)
            (mvch :: Bool)
            (att  :: k)
            (vp   :: Type)
            (lcht :: (k,Type))
            (vch  :: [(k, Type)])  where
  type CopyR' mnts mvch att vp lcht vch :: [(k, Type)]
  cpychi' :: Proxy mnts
          -> Proxy mvch
          -> Label att
          -> vp
          -> Label lcht
          -> Attribution vch
          -> Attribution (CopyR' mnts mvch att vp lcht vch)



instance Copy' False mvch att vp lcht pch where
  type CopyR' False mvch att vp lcht pch = pch
  cpychi' _ _ _ _ _ pch = pch

instance Copy' True True att vp lcht pch where
  type CopyR' True True att vp lcht pch = pch
  cpychi' _ _ _ _ _ pch = pch

instance (LabelSet ('(att, vp) : pch))
  => Copy' True False att vp lcht pch where
  type CopyR' True False att vp lcht pch
      = '(att, vp) ': pch
  cpychi' _ _ att vp _ pch = (att =. vp .*. pch) 



--------------------------------------------------------------------------


-- data Modes (att :: k) (nts :: [(k,Type)])
--            (op :: Type) (unit :: Type) where
--   FnSynT :: Label att -> Modes att nts op unit
--   -- | FnInhT att nts
--   -- | FnUseT att nts op unit
--   -- deriving Show


-- data family Demote (t :: Modes att nts op unit) :: Type
-- data instance Demote (FnSynT att)
--   = FnSyn att 
-- --data instance Demote (FnInhT att nts)  = FnInh att nts


-- -- class Apply ic f a where
-- --   type ApplyR ic f a

-- -- instance (Defs att nts vals ic)
-- --   => Apply ic (FnInhT att nts) (Fam sc ip -> Record vals) where
-- --   type ApplyR ic (FnInhT att nts) (Fam sc ip -> Record vals)
-- --     = forall sp. Rule sc ip ic sp (DefsR att nts vals ic) sp

-- data F att nts = F att nts

app att nts f = inhdef att nts . f
--app' (FnSyn att) f = syndef att . f



-- data DefMode
--   = FnInhMode
--   | FnSynMode
--   deriving Show

-- data family DemoteMode (mode :: DefMode)
--                        (att  :: k)
--                        (nts  :: [Type])
--                        (m    :: Type)          :: Type

-- data instance DemoteMode FnInhMode att nts m where
--   FnInh :: Label att -> HList nts -> DemoteMode FnInhMode att nts m

-- data instance DemoteMode FnSynMode att nts m where
--   FnSyn :: Label att -> DemoteMode FnSynMode att nts m

-- class Apply mode att nts m vals a ic sp where
--   type ApplyR mode att nts m vals a ic sp
--   apply :: DemoteMode mode att nts m
--         -> (a -> Record vals)
--         -> a
--         -> Fam ic sp
--         -> ApplyR mode att nts m vals a ic sp

-- instance (Defs att nts vals ic)
--   => Apply FnInhMode att nts m vals a ic sp where
--   type ApplyR FnInhMode att nts m vals a ic sp
--     = Fam (DefsR att nts vals ic) sp
--   apply (FnInh att nts) f = inhdef att nts . f


-- -- Instance Apply FnSynMode att nts m vals a ic sp where
-- --   type ApplyR FnSynMode att nts m vals a ic sp


-- class DefAspUse (att  :: k)
--                 (nts  :: [Type])
--                 (a    :: Type)
--                 (prds :: [Type]) where
--   type DefAspUseR att nts a prds :: [(Type, Type)]
--   defAspUse :: Label att -> HList nts
--             -> (a -> a -> a) -> a
--             -> HList prds
--             -> Aspect (DefAspUseR att nts a prds)

-- instance DefAspUse att nts a '[] where
--   type DefAspUseR att nts a '[] = '[]
--   defAspUse _ _ _ _ _ = EmptyR


-- instance (DefAspUse att nts a prds)
--   => DefAspUse att nts a (prd ': prds) where
--   type DefAspUseR att nts a (prd ': prds)
--     =( '(prd , Any)
--        ': DefAspUseR att nts a prds)
--   defAspUse att nts op unit (HCons prd prds)
--     = (prd .=. defAspUse1 att nts prd op unit) .*. defAspUse att nts op unit prds


-- class DefAspUse1 att nts prd a sc sp where
--   type DefAspUse1R att nts prd a sc sp :: Type
--   defAspUse1 :: Label att -> HList nts ->
--     Label prd -> (a -> a -> a) -> a -> Fam sc ip
--     -> (Fam ic sp -> Fam ic ( '(att, a) ': sp))

-- instance ( Use att nts a sc
--          , LabelSet ('(att, a) : sp))
--   => DefAspUse1 att nts prd a sc sp where
--   type DefAspUse1R att nts prd a sc sp = () 
--   defAspUse1 att nts prd op unit (Fam sc _)
--     = let res = usechi att nts op sc
--       in (syndef att (maybe unit id res))
          

data Rec (c :: k) (r :: [(k', k'')]) :: Type where
  EmptyRec :: Rec c '[]
  ConsRec  :: LabelSet ( '(l,v) ': r) =>
              TagField c l v -> Rec c r -> Rec c ( '(l,v) ': r)

data TagField (cat :: k) (l :: k') (v :: k'') where
  TagField :: Label c -> Label l -> WrapField c v -> TagField c l v

untagField :: TagField c l v -> WrapField c v
untagField (TagField lc lv v) = v

data ChiRec; data Attrib; data Reco

field1  :: TagField Reco L1 Bool
field1  =  TagField Label Label False
field2  :: TagField Reco L2 Char
field2  =  TagField Label Label '4'
data L1 
data L2
data L3
data L4
type Re = Rec Tagged
r1 = field1 `ConsRec` (field2 `ConsRec` EmptyRec)


type family    WrapField (c :: Type)  (v :: k) -- = ftype | ftype c -> v
type instance  WrapField Reco    (v :: Type) = v
type instance  WrapField Attrib  (v :: Type) = v
type instance  WrapField ChiRec  (v :: [(k, Type)]) = Attribution v

{-
Node:
We cannot encode the dependency {ftype, c} -> v since TypeFamilyDependencies
does not support this general dependencies. So from (WrapField c v) we
can't infer c.

-}



-- class WrapFieldC (t :: Type)  (v :: k) where
--   type WrapField' t v :: Type
--   wrapfield :: WrapField' t v -> 


data OpLookup (c :: Type)
              (l  :: k)
              (r  :: [(k, k')]) :: Type where
  OpLookup :: Label l -> Rec c r -> OpLookup c l r

data OpLookup' (b  :: Bool)
               (c  :: Type)
               (l  :: k)
               (r  :: [(k, k')]) :: Type where
  OpLookup' :: Proxy b -> Label l -> Rec c r -> OpLookup' b c l r


class Require (op   :: Type)
              (ctx  :: [Symbol])  where
   type ReqR op
   req :: Proxy ctx -> op -> ReqR op

instance (Require (OpLookup' (l == l') c l ( '(l', v) ': r)) ctx)
  => Require (OpLookup c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup c l ( '(l', v) ': r))
    = ReqR (OpLookup' (l == l') c l ( '(l', v) ': r))
  req ctx (OpLookup l r) = req ctx (OpLookup' (Proxy @ (l == l')) l r)

instance Require (OpLookup' 'True c l ( '(l, v) ': r)) ctx where
  type ReqR (OpLookup' 'True c l ( '(l, v) ': r)) = WrapField c v
  req Proxy (OpLookup' Proxy Label (ConsRec f _)) = untagField f

instance (Require (OpLookup c l r) ctx)
  => Require (OpLookup' False c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup' False c l ( '(l', v) ': r)) = ReqR (OpLookup c l r)
  req ctx (OpLookup' Proxy l (ConsRec _ r)) = req ctx (OpLookup l r)

                                              


-- el mensaje no tiene sentido, solo para testear:
instance (TypeError (Text "field not Found on Record,"
                    :<>: Text "looking up the label: " :<>: ShowType l
                    :$$: Text "from the use of " :<>: Text ctx))
  => Require (OpLookup Reco l '[]) '[ctx] where {}

instance (TypeError (Text "field not Found on Record,"
                    :<>: Text "updating the label: " :<>: ShowType l
                    :$$: Text "from the use of " :<>: Text ctx))
  => Require (OpUpdate Reco l v '[]) '[ctx] where {}

-- -- req (Proxy @ '["lolo"]) (OpLookup (Label @ Char) r1)<<<----probar esto :) 
-- instance (TypeError (Text "Error: " :<>: Text txt :<>:
--                      Text "from context:" :<>: Text ctx))
--   => Require (OpError txt) '[ctx]

-- | update

data OpUpdate (c  :: Type)
              (l  :: k)
              (v  :: k')
              (r  :: [(k, k')]) :: Type where
  OpUpdate :: Label l -> WrapField c v -> Rec c r
           -> OpUpdate c l v r

data OpUpdate' (b  :: Bool)
               (c  :: Type)
               (l  :: k)
               (v  :: k')
               (r  :: [(k, k')]) :: Type where
  OpUpdate' :: Proxy p -> Label l {- -> Proxy v-}-> WrapField c v ->  Rec c r
           -> OpUpdate' b c l v r

{- Look at the comment above, WrapField c v is not enough to recover
v, that's why we use an extra proxy

update: Instead of the proxy, I use TypeApplications below

-}

instance (Require (OpUpdate' (l == l') c l v ( '(l', v') ': r) ) ctx )
  => Require (OpUpdate c l v ( '(l', v') ': r) ) ctx where
  type ReqR (OpUpdate c l v ( '(l', v') ': r) )
    = ReqR (OpUpdate' (l == l') c l v ( '(l', v') ': r) )
  req ctx (OpUpdate l f r)
    = (req @(OpUpdate' (l == l') _ _ v _ )) -- v is explicity instantiated 
       ctx (OpUpdate' (Proxy @(l == l')) l f r)


instance ( LabelSet ( '(l, v) ': r)
         , LabelSet ( '(l, v') ': r))
  => Require (OpUpdate' 'True c l v ( '(l, v') ': r)) ctx where
  type ReqR (OpUpdate' 'True c l v ( '(l, v') ': r))
    = Rec c ( '(l, v) ': r)
  req ctx (OpUpdate' proxy label field (ConsRec tgf r))
    = ConsRec (TagField Label label field) r

-- instance ( Require (OpUpdate c l v r) ctx
--          , ConsFam l' v' (ReqR (OpUpdate c l v r)) ~ Rec c ( '(l', v') : r0)
--          , ReqR (OpUpdate c l v r) ~ Rec c r0
--          , LabelSet ( '(l', v') : r0)
--          )
--   => Require (OpUpdate' 'False c l v ( '(l',v') ': r)) ctx where
--   type ReqR (OpUpdate' 'False c l v ( '(l',v') ': r))
--     = ConsFam l' v' (ReqR (OpUpdate c l v r))
--   req ctx (OpUpdate' _ l f (ConsRec field r))
--     = ConsRec field $ (req @(OpUpdate _ _ v r)) ctx (OpUpdate l f r)

---type family ConsFam (l :: k) (v :: k') r
---type instance ConsFam l v (Rec c r) = Rec c ( '(l,v) ': r)


instance ( Require (OpUpdate c l v r) ctx
         , UnWrap (ReqR (OpUpdate c l v r)) ~ r0
         , LabelSet ( '(l', v') : r0)
         , ReqR (OpUpdate c l v r) ~ Rec c r0)
  => Require (OpUpdate' 'False c l v ( '(l',v') ': r)) ctx where
  type ReqR (OpUpdate' 'False c l v ( '(l',v') ': r))
    = Rec c ( '(l',v') ': (UnWrap (ReqR (OpUpdate c l v r))))
  req ctx (OpUpdate' _ l f (ConsRec field r))
    = ConsRec field $ (req @(OpUpdate _ _ v r)) ctx (OpUpdate l f r)


{- to manipulate cons at type level in a generic way -}

type family UnWrap t :: [(k,k')]
type instance UnWrap (Rec c r) = r
