> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE FlexibleContexts  #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}

> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# LANGUAGE DataKinds #-}

> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE EmptyDataDeriving #-}

> module Hoas where


> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH


> type Name = String

> data TType
>   = TBool | TInt
>   deriving (Show, Eq, Read)

> data BOp
>   = OOr | OAnd | OEq | OLT | OPlus | OMinus | OTimes | ODiv | OMod
>   deriving (Show, Eq, Read)

> data UOp
>   = ONot | OOp
>   deriving (Show, Eq, Read)

> $(addNont "Program")
> $(addNont "Defs"); $(addNont "DefList")
> $(addNont "Body"); $(addNont "StmtList")
> $(addNont "Stmt")
> $(addNont "Expr")


> $(addProd "Program" ''Nt_Program [("programName", Ter ''Name),
>                                   ("programDefs", NonTer ''Nt_Defs),
>                                   ("programBody", NonTer ''Nt_Body)])

> $(addProd "EmptyDef" ''Nt_DefList [])
> $(addProd "ConsDef" ''Nt_DefList  [("varName", Ter ''Name),
>                                    ("varType", Ter ''TType),
>                                    ("tailDefList", NonTer ''Nt_Defs)])
> $(addProd "Defs" ''Nt_Defs [("defList", NonTer ''Nt_DefList)])


> $(addProd "ConsStmt"    ''Nt_StmtList [("headStmt", NonTer ''Nt_Stmt),
>                                        ("tailStmtList", NonTer ''Nt_StmtList)])
> $(addProd "SingleStmt"  ''Nt_StmtList [("stmtLast", NonTer ''Nt_Stmt)] )
> $(addProd "Body" ''Nt_Body [("bodyStmts", NonTer ''Nt_StmtList)])


> $(addProd "Assign" ''Nt_Stmt [("assignName", Ter ''Name),
>                               ("assignExpr", NonTer ''Nt_Expr)])
> $(addProd "If" ''Nt_Stmt [("ifCond", NonTer ''Nt_Expr),
>                           ("ifThen", NonTer ''Nt_Body),
>                           ("ifElse", NonTer ''Nt_Body)])
> $(addProd "While" ''Nt_Stmt [("whileCond", NonTer ''Nt_Expr),
>                              ("whileDo" , NonTer ''Nt_Body)])
> $(addProd "WriteLn" ''Nt_Stmt [("writeLnExpr", NonTer ''Nt_Expr)])
> $(addProd "ReadLn" ''Nt_Stmt [("readLnName", Ter ''Name)])

> $(addProd "Var" ''Nt_Expr [("litName", Ter ''Name)])
> $(addProd "Bool" ''Nt_Expr [("litBool", Ter ''Bool)])
> $(addProd "NatL" ''Nt_Expr [("litNat", Ter ''Int)])
> $(addProd "BOpExpr" ''Nt_Expr [("l", NonTer ''Nt_Expr),
>                                ("bop", Ter ''BOp),
>                                ("r", NonTer ''Nt_Expr)])
> $(addProd "UOpExpr" ''Nt_Expr [("uop", Ter ''UOp),
>                                ("e", NonTer ''Nt_Expr)])

> $(closeNTs [''Nt_Program, ''Nt_Body, ''Nt_StmtList,
>             ''Nt_DefList, ''Nt_Defs, ''Nt_Stmt, ''Nt_Expr])

> $(mkSemFuncs [''Nt_Program, ''Nt_Body, ''Nt_StmtList,
>             ''Nt_DefList, ''Nt_Defs, ''Nt_Stmt, ''Nt_Expr])


Example: pretty printing expressions

> $(attLabel "sshow" ''String)

> showExpr :: Expr -> String
> showExpr e = (sem_Expr asp_showExpr e EmptyAtt) #. sshow

> asp_showExpr
>  =   (syn sshow p_NatL $ show <$> ter ch_litNat)
>  .+: (syn sshow p_Bool $ show <$> ter ch_litBool)
>  .+: (syn sshow p_Var  $ ter ch_litName)
>  .+: (syn sshow p_BOpExpr $
>      do l  <- at ch_l sshow
>         op <- ter ch_bop
>         r  <- at ch_r sshow
>         let wrap s = " " ++ s ++ " "
>         return $ "(" ++ l ++ wrap (show op) ++ r ++ ")"
>      )
>  .+: (syn sshow p_UOpExpr $
>      do op <- ter ch_uop
>         e  <- at ch_e sshow
>         return $ "(" ++ show op ++ " " ++ e ++ ")"
>      )
>  .+: emptyAspect

> test = showExpr (BOpExpr (Var "x") OOr $ UOpExpr ONot $ Bool True)
