{-# LANGUAGE TemplateHaskell, CPP #-}
{-# OPTIONS -XEmptyDataDecls #-}

module Data.AspectAG.Derive (deriveAG, attLabel, attLabels, chLabel, chLabels, typeList) where

import Language.Haskell.TH

import Data.Set (Set)
import Data.List (isPrefixOf)
import qualified Data.Set as S

import Data.AspectAG

data UserType  = UserD Name [Name] [Con]
type TypeDecls = (Set Name, [Dec])


declareLabel :: Name -> Name -> TypeQ -> Q [Dec]
declareLabel ndata nlabel t = do 
            dtl <- dataD (cxt []) ndata [] [] []
            lbl <- declareFnLabel nlabel t
            return $ dtl:lbl

declareFnLabel ::  Name -> TypeQ -> Q [Dec]
declareFnLabel nlabel t = do 
            sgn <- sigD nlabel (appT (conT $ mkName "Proxy") t)  
            let pxy = normalB [| proxy |]
            lbl <- funD nlabel [clause [] pxy []]
            return [sgn,lbl]

attLabel ::  String -> Q [Dec]
attLabel att = declareLabel attn (mkName att) (conT $ attn) 
  where
      attn  = mkName $ "Att_" ++ att
      

attLabels ::  [String] -> Q [Dec]
attLabels = liftM concat . mapM attLabel

chLabel ::  String -> Name -> Q [Dec]
chLabel n t = chLabels [n] t

chLabels ::  [String] -> Name -> Q [Dec]
chLabels ns t = (liftM concat) $ mapM (label t . mkName) ns
  where
      label t n = declareLabel (chTName n) (chName n) (tyLabel (chTName n) t) 
      tyLabel n t = appT (appT (conT $ mkName "(,)") (conT n)) (conT t) 


chLabels2 ::  [Name] -> [Type] -> Q [Dec]
chLabels2 ns ts = (liftM concat) $ zipWithM label ns ts
  where
      label n t = declareLabel (chTName n) (chName n) (tyLabel (chTName n) t) 
      tyLabel n t = appT (appT (conT $ mkName "(,)") (conT n)) (return t) 

chName,chTName,ntName,prdName,prdTName ::  Name -> Name
chName   cn = mkName $ "ch_" ++ nameBase cn 
chTName  cn = mkName $ "Ch_" ++ nameBase cn 
ntName   cn = mkName $ "nt_" ++ nameBase cn 
prdName  cn = mkName $ "p_"  ++ nameBase cn 
prdTName cn = mkName $ "P_"  ++ nameBase cn 


deriveAG :: Name -> Q [Dec]
deriveAG n = do
              (_,decl) <- derive n (S.empty,[]) --eval)
              return decl




semName ::  Name -> Name
semName t = mkName ("sem_"++(nameBase t))

derive :: Name -> TypeDecls -> Q TypeDecls 
derive n (stn,decl) = 
    do
       info <- reify n 
       if (S.member n stn || not (isNT info))  
          then return (stn,decl)
          else let stn' = S.insert n stn
               in  do
                      (UserD _ _ lc) <- getUserType info
                      ((s,d),fc)   <- foldM deriveCons ((stn',decl),[]) lc
                      let semDecl = FunD (semName n) fc
                      nt <- declareFnLabel (ntName n) (conT $ n)
                      return (s,semDecl:(nt++d))

deriveCons :: (TypeDecls,[Clause]) -> Con -> Q (TypeDecls,[Clause])
deriveCons ((stn,decl),fc) c =                     
    do
      let (cht,chn,cn) = getCtx c
      (stn',decl') <- foldM (\td t -> deriveList (typeNames t) td) (stn,decl) cht
      conargs <- newNames cht
      body <- [| knit ($(aspV) # $(att cn)) $(childs cht chn conargs) |] 
      let semF = Clause (pat cn conargs) (NormalB body) []
      lp <- declareLabel (prdTName cn) (prdName cn) (conT $ prdTName cn)
      lc <- chLabels2 chn cht
      return ((stn',lp++lc++decl'),semF:fc)
  where
     newNames []     = return []
     newNames (_:as) = do
                        na  <- newName "x"
                        nas <- newNames as
                        return (na:nas)
     pat cn args = [aspP, ConP cn (map VarP args)] 
     aspP = VarP $ mkName "asp"
     aspV = varE $ mkName "asp"
     att cn  = varE $ prdName cn
     ch  cn  = varE $ chName cn
     childs []     _      _      = [| emptyRecord |]
     childs (t:ts) (n:ns) (p:ps) = case (typeName1 t) of
                                     Just tn -> [| $(ch n) .=. $(chFun tn p)  .*. $(childs ts ns ps) |]
                                     Nothing -> [| $(childs ts ns ps) |]
     childs _      _      _      = error "Impossible case!!"
     deriveList ns td = foldM (flip $ derive) td ns
     chFun tn n =  
              do
                  i <- reify (tn)
                  if isNT i
                   then [| $(varE (semName tn)) $(aspV) $(varE n) |]
                   else [| ( \(Record HNil) -> $(varE n) ) |]
           



#if __GLASGOW_HASKELL__ < 612 
getUserType :: Info -> Q UserType
getUserType info = do
    case info of
        TyConI d -> case d of
            (DataD     _ uname args cs  _)  -> return $ UserD uname args cs 
            (NewtypeD  _ uname args c   _)  -> return $ UserD uname args [c]
            _                               -> scopeError
        _ -> scopeError
    where scopeError = error $ "Can only be used on algebraic datatypes"
#endif

#if __GLASGOW_HASKELL__ >= 612
getUserType :: Info -> Q UserType
getUserType info = do
    case info of
        TyConI d -> case d of
            (DataD     _ uname args cs  _)  -> return $ UserD uname (map f args) cs 
            (NewtypeD  _ uname args c   _)  -> return $ UserD uname (map f args) [c]
            _                               -> scopeError
        _ -> scopeError
    where scopeError = error $ "Can only be used on algebraic datatypes"
          f (PlainTV n)    = n
          f (KindedTV n _) = n
#endif

getCtx :: Con -> ([Type],[Name], Name) 
getCtx (RecC           name args) = (map thd args, map fst' args, name)
getCtx (NormalC name []) = ([],[],name)
getCtx (NormalC name _)  = error $ "Constructor " ++ (show name) ++ " is not a record."
getCtx (InfixC _ name _) = error $ "Constructor " ++ (show name) ++ " is not a record."	
getCtx _ = error $ "Cannot derive a 'forall' constructor."	

thd :: (a, b, c) -> c
thd (_, _, c) = c

fst' :: (a, b, c) -> a
fst' (a, _, _) = a



isNT ::  Info -> Bool
isNT (PrimTyConI _ _ _)          =  False
isNT (TyConI (DataD _ n _ _ _))  =  not $ isPrefixOf "GHC" (show n) -- GHC types can't be non-terminals
isNT (TyConI (TySynD _ _ _))     =  False   -- type synonyms to escape
isNT  _                          =  True


typeNames :: Type -> [ Name ]
typeNames t = case t of
    VarT _                   -> [  ]
    ConT conname             -> [ conname ]
    AppT t1 t2               -> typeNames t1 ++ typeNames t2
    _                        -> error $ "Not valid type " ++ (show t)


typeName1 :: Type -> Maybe Name 
typeName1 t = case t of
    VarT _                   -> Nothing
    ConT conname             -> Just conname
    AppT t1 _                -> typeName1 t1
    _                        -> error $ "Not valid type " ++ (show t)



typeList :: String -> String -> Q [Dec]
typeList nData nArg =  
   do
     let ddef = DataD [] dataName [] [ RecC consName [(hdName, NotStrict, ConT argName), (tlName ,NotStrict, ConT dataName) ]
                                     , NormalC nilName []] []
     return [ ddef ]
 where
  dataName = mkName nData
  argName  = mkName nArg
  consName = mkName $ "Cons" ++ nData
  nilName  = mkName $ "Nil"  ++ nData
  hdName   = mkName $ "hd"   ++ nData
  tlName   = mkName $ "tl"   ++ nData



  
