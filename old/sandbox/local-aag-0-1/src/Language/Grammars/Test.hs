{-# OPTIONS -XMultiParamTypeClasses -XFunctionalDependencies 
            -XFlexibleContexts -XFlexibleInstances 
            -XUndecidableInstances 
            -XExistentialQuantification 
            -XEmptyDataDecls -XRank2Types
            -XTypeSynonymInstances #-}



class DF a b c | a b -> c where
instance (DF' a r' r'',DF' (Maybe a,a') r'' r, DF c b r')
          => DF ((a,a'),c) b r

class DF' a b c | a b -> c where


--   of the corresponding child. 
class Defs nts vals ic ic'  | nts vals ic -> ic' where
  --defs :: att -> nts -> vals -> ic -> ic'

instance  ( Defs nts vs ic ic'
          ,  DF (lch,t) ic' mch
          ,  DF' t nts mnts
          , SingleDef mch mnts 
                  ((lch,t), vch) 
                  ic' ic'' ) 
      => Defs nts 
              (((lch,t), vch), vs) 
              ic ic'' 
       where 
    --    defs = undefined

class  SingleDef mch mnts pv ic ic' 
       | mch mnts pv ic -> ic' 
  --where singledef :: mch -> mnts -> att -> pv -> ic -> ic'


data Chi a b
