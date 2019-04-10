{-# LANGUAGE TemplateHaskell, CPP, DataKinds, FlexibleInstances #-}
{-# OPTIONS -XEmptyDataDecls #-}

module Language.Grammars.AspectAG.Derive where

import Language.Haskell.TH

import Data.List
import Data.Set (Set)
import Data.List (isPrefixOf, isSuffixOf, sort)
import qualified Data.Set as S

import Language.Grammars.AspectAG
import Control.Monad

import qualified Language.Haskell.TH.Compat.Strict as Comp

-- import Debug.Trace

data UserType  = UserD Name [Name] [Con]
type TypeDecls = (Set Name, [Dec])


declareLabel :: Name -> Name -> TypeQ -> Q [Dec]
declareLabel ndata nlabel t = do 
            dtl <- dataD (cxt []) ndata [] Nothing [] []
            lbl <- declareFnLabel nlabel t
            return $ dtl:lbl

declareFnLabel ::  Name -> TypeQ -> Q [Dec]
declareFnLabel nlabel t = 
             do sgn <- sigD nlabel (appT (conT $ mkName "Label") t)  
                let pxy = normalB [| Label |]
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
chLabels ns ty = (liftM concat) $ mapM (label ty . mkName) ns
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


extendAG :: Name -> [Name] -> Q [Dec]
extendAG n used = do
              (_,decl) <- derive n (S.fromList(used),[]) --eval)
              return decl

addNT :: String -> Q [Dec]
addNT nt = declareLabel ntn (ntName ntn ) (conT $ ntn)
    where ntn = mkName nt

addProd :: String -> [ (String, Name) ] -> Q [Dec]
addProd prod children = do
                let pn = mkName prod
                p  <- declareLabel (prdTName pn) (prdName pn) (conT $ prdTName pn)
                ch <- (liftM concat . mapM (\(a,b) -> chLabel a b)) children

                conargs <- newNames children
                bodyP <- [| knit $(aspV) $(childsP (map (mkName . fst) children) conargs) |] 
                let semFCons = FunD (semPName pn) 
                                    [(Clause (aspP:(map VarP conargs)) (NormalB bodyP) [])]


                return (semFCons:p++ch)

semName ::  Name -> Name
semName t = mkName ("sem_"++(nameBase t))

semPName ::  Name -> Name
semPName t = mkName ("semP_"++(nameBase t))

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
                      if (isPrefixOf "EXT" (nameBase n))  -- type extensions start with EXT
                       then return (s,d)                      
                       else do let semDecl = FunD (semName n) fc
                               nt <- declareFnLabel (ntName n) (conT $ n)
                               return (s,semDecl:(nt++d))

deriveCons :: (TypeDecls,[Clause]) -> Con -> Q (TypeDecls,[Clause])
deriveCons ((stn,decl),fc) c =                     
    do
      let (cht,chn,cn) = getCtx c
      (stn',decl') <- foldM (\td t -> deriveList (typeNames t) td) (stn,decl) cht
      conargs <- newNames cht
      body <- [| knit ($(aspV) .#. $(attVar cn)) $(childs cht chn conargs) |]
      bodyP <- [| knit $(aspV) $(childsP chn conargs) |] 
      let semF = Clause (pat cn conargs) (NormalB body) []
      let semFCons = FunD (semPName cn) 
                          [(Clause (aspP:(map VarP conargs)) (NormalB bodyP) [])] 
      lp <- declareLabel (prdTName cn) (prdName cn) (conT $ prdTName cn)
      lc <- chLabels2 chn cht
      return ((stn',semFCons:(lp++lc++decl')),semF:fc)


newNames ::  [t] -> Q [Name]
newNames []     = return []
newNames (_:as) = do
                   na  <- newName "x"
                   nas <- newNames as
                   return (na:nas)

pat ::  Name -> [Name] -> [Pat]
pat cn args | isSuffixOf ("_Cons") (nameBase cn) = [aspP, InfixP (VarP $ args !! 0) (mkName ":") (VarP $ args !! 1) ]
            | isSuffixOf ("_Nil")  (nameBase cn) = [aspP, ListP [] ]
            | isSuffixOf ("_Just") (nameBase cn) = [aspP, ConP (mkName "Just") (map VarP args) ]
            | isSuffixOf ("_Nothing")  (nameBase cn) = [aspP, ConP (mkName "Nothing") [] ]
            | otherwise =  [aspP, ConP cn (map VarP args)] 

aspP ::  Pat
aspP = VarP $ mkName "asp"
aspV ::  ExpQ
aspV = varE $ mkName "asp"
attVar ::  Name -> ExpQ
attVar cn  = varE $ prdName cn
chVar ::  Name -> ExpQ
chVar  cn  = varE $ chName cn

childs ::  [Type] -> [Name] -> [Name] -> Q Exp
childs []     _      _      = [| emptyRecord |]
childs (t:ts) (n:ns) (p:ps) = case (typeName1 t) of
                                Just tn -> [| $(chVar n) .=. $(chFun tn p)  .*. $(childs ts ns ps) |]
                                Nothing -> [| $(childs ts ns ps) |]
childs _      _      _      = error "Impossible case!!"

childsP ::  [Name] -> [Name] -> Q Exp
childsP []     _      = [| emptyRecord |]
childsP (n:ns) (p:ps) = [| $(chVar n) .=. $(varE p)  .*. $(childsP ns ps) |]
childsP _      _      = error "Impossible case!!"

deriveList ::  [Name] -> TypeDecls -> Q TypeDecls
deriveList ns td = foldM (flip $ derive) td ns

chFun ::  Name -> Name -> Q Exp
chFun tn n =  
         do
             i <- reify (tn)
             if isNT i
              then [| $(varE (semName tn)) $(aspV) $(varE n) |]
              -- else [| ( \(EmptyR) -> $(varE n) ) |]
              else [| ( sem_Lit $(varE n)  ) |]



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
            (DataD     _ uname args _ cs  _)  -> return $ UserD uname (map f args) cs 
            (NewtypeD  _ uname args _ c   _)  -> return $ UserD uname (map f args) [c]
            (TySynD    uname args t)        -> let  name = nameBase uname
                                                    cs = case t of
                                                                (AppT ListT lt) -> [ NormalC (mkName $ name ++ "_Nil") []
                                                                                   , RecC (mkName $ name ++ "_Cons") 
                                                                                          [ (mkName ("hd_" ++ name ++ "_Cons"),Comp.notStrict,lt) 
                                                                                          , (mkName ("tl_" ++ name ++ "_Cons"),Comp.notStrict,ConT uname) ]]
                                                                (AppT (ConT nt) pt) ->
                                                                            case (nameBase nt) of
                                                                                "Maybe" ->   [ NormalC (mkName $ name ++ "_Nothing") []
                                                                                             , RecC (mkName $ name ++ "_Just") 
                                                                                                    [ (mkName ("just_" ++ name ++ "_Just"),Comp.notStrict,pt) ]]
                                                                                _ -> error "Not allowed type synonym"
                                                                _ -> error "Not allowed type synonym"
                                               in   return (UserD uname (map f args) cs)
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


-- | isNT decides if a Type is a Terminal. Types defined by the programmer
-- starting with "T_" are considered terminals
isNT ::  Info -> Bool
isNT (PrimTyConI _ _ _)          =  False
isNT (TyConI (DataD _ n _ _ _ _))  =  not (isPrefixOf "GHC" (show n)
                                           || (isSubsequenceOf "T_" (show n)))       -- GHC types can't be non-terminals
isNT (TyConI (TySynD n _ _))     =  ((not (isPrefixOf "GHC" (show n))) &&    -- GHC types can't be non-terminals
                                    (not (isPrefixOf "GHC" (nameBase n))))   -- type synonyms starting with GHC to escape (example: GHC_MyType)
                                 
-- otherwise theew is a terminal
isNT  _                          =  True


typeNames :: Type -> [ Name ]
typeNames t = case t of
    VarT _                   -> [  ]
    ConT conname             -> [ conname ]
    AppT t1 t2               -> typeNames t1 ++ typeNames t2
    ListT                    -> [ ]
    _                        -> error $ "Not valid type " ++ (show t)


typeName1 :: Type -> Maybe Name 
typeName1 t = case t of
    VarT _                   -> Nothing
    ConT conname             -> Just conname
    AppT t1 _                -> typeName1 t1
    ListT                    -> Nothing
    _                        -> error $ "Not valid type " ++ (show t)



mkNames (_,fields,cname) = ( mkName ('p' : nameBase cname)
                           , mkName ('_' : nameBase cname)
                           , map (\n -> mkName ('_' : nameBase n)) fields)

recField (pc,c,fs) = (pc, Comp.notStrict, foldr (\n t -> AppT (AppT ArrowT (VarT n)) t) (VarT c) fs)

deriveLang :: String -> [Name] -> Q [Dec]
deriveLang l ns =  undefined
  -- let recName = mkName (l ++ "SF")
  -- in  do cs <- mapM getCs ns 
  --        let names = sort $ map (mkNames . getCtx) (concat cs)
  --        let ts = map (\(_,c,fs) -> (PlainTV c) : (map PlainTV fs)) names
  --        let rec = DataD [] recName (concat ts) [RecC recName (map recField names) ] []
  --        let semp t = VarE $ mkName ("semP"++(nameBase t))
  --        let body = NormalB $ RecConE recName (map  (\(pc,_c,_) -> (pc, AppE (semp _c) (VarE _c)) ) names)
  --        let mk  = FunD  (mkName ("mk" ++ l)) [ Clause (map (\(_,c,_) -> VarP c) names) body [] ]
  --        return [ rec, mk ]

getCs n = undefined
  -- =  do info <- reify n 
  --       (UserD _ _ lc) <- getUserType info
  --       return lc




class SemLit a where
  sem_Lit :: a -> Attribution p -> Attribution '[ '(a, a)]
  lit     :: Label (a)
instance SemLit a where
  sem_Lit a _ = (Label =. a) *. emptyAtt
  lit         = Label 
