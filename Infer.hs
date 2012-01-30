{-# LANGUAGE PackageImports #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Infer where

import Logic
import LogicList

import Control.Applicative
import Control.Monad
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State

type Variable = String 

data Exp = VarE (LogicVal Variable)
         | IntE (LogicVal Int)
         | BoolE (LogicVal Bool)
         | IsZeroE (LogicVal Exp)
         | PredE (LogicVal Exp)
         | MultE (LogicVal Exp) (LogicVal Exp)
         | IfE (LogicVal Exp) (LogicVal Exp) (LogicVal Exp)
         | LamE (LogicVal Variable) (LogicVal Exp)
         | AppE (LogicVal Exp) (LogicVal Exp)
           deriving (Eq, Show)

instance Unifiable Exp where
  unify x y = do
    s <- getSubst
    case (walk x s, walk y s) of
      (x', y') | x' == y' -> return ()
      (Var id, y') -> modifySubst (extendS (Var id) y')
      (x', Var id) -> modifySubst (extendS (Var id) x')
      (Val (VarE x), Val (VarE y)) -> unify x y
      (Val (IntE x), Val (IntE y)) -> unify x y
      (Val (BoolE x), Val (BoolE y)) -> unify x y
      (Val (IsZeroE x), Val (IsZeroE y)) -> unify x y
      (Val (PredE x), Val (PredE y)) -> unify x y
      (Val (MultE x1 x2), Val (MultE y1 y2)) ->
        unify x1 y1 >> unify x2 y2
      (Val (IfE xt xc xa), Val (IfE yt yc ya)) ->
        unify xt yt >> unify xc yc >> unify xa ya
      (Val (LamE x xbody), Val (LamE y ybody)) ->
        unify x y >> unify xbody ybody
      (Val (AppE xrator xrand), Val (AppE yrator yrand)) ->
        unify xrator yrator >> unify xrand yrand
      _ -> mzero

instance Reifiable Exp where
  reify lv = do
    s <- ask
    case walk lv s of
      Val (VarE x) -> Val . VarE <$> reify x
      Val (IntE x) -> Val . IntE <$> reify x
      Val (BoolE x) -> Val . BoolE <$> reify x
      Val (IsZeroE x) -> Val . IsZeroE <$> reify x
      Val (PredE x) -> Val . PredE <$> reify x
      Val (MultE x1 x2) -> Val <$> (MultE <$> reify x1 <*> reify x2)
      Val (IfE t c a) -> Val <$> (IfE <$> reify t <*> reify c <*> reify a)
      Val (LamE x body) -> Val <$> (LamE <$> reify x <*> reify body)
      Val (AppE rator rand) -> Val <$> (AppE <$> reify rator <*> reify rand)
      Var id -> reifyVar (Var id)

data Typ = IntT | BoolT | FunT (LogicVal Typ) (LogicVal Typ)
         deriving (Eq, Show)

instance Unifiable Typ where
  unify x y = do
    s <- getSubst
    case (walk x s, walk y s) of
      (x', y') | x' == y' -> return ()
      (Var id, y') -> modifySubst (extendS (Var id) y')
      (x', Var id) -> modifySubst (extendS (Var id) x')
      (Val (FunT x1 x2), Val (FunT y1 y2)) -> unify x1 x2 >> unify y1 y2
      _ -> mzero

instance Reifiable Typ where
  reify lv = do
    s <- ask
    case walk lv s of
      Val (FunT t1 t2) -> do
        t1' <- reify t1
        t2' <- reify t2
        return $ Val (FunT t1' t2')
      Val x -> return $ Val x
      Var id -> reifyVar (Var id)      

type TypEnv = LogicList (LogicVal (LogicVal Variable, LogicVal Typ))

lookupEnv :: LogicVal Variable
          -> LogicVal TypEnv
          -> LogicVal Typ
          -> LogicComp ()
lookupEnv x gamma t =
  msum [ do gamma' <- var
            gamma ==@ Cons (Val (x, t)) gamma'
       , do y <- var
            yt <- var
            gamma' <- var
            gamma ==@ Cons (Val (y, yt)) gamma'
            lookupEnv x gamma' t
       ]

infer :: LogicVal TypEnv
      -> LogicVal Exp
      -> LogicVal Typ
      -> LogicComp ()
infer gamma exp t =
  msum [ do x <- var
            exp ==@ VarE x
            lookupEnv x gamma t
       , do n <- var
            exp ==@ IntE n
            t ==@ IntT
       , do b <- var
            exp ==@ BoolE b
            t ==@ BoolT
       , do e <- var
            exp ==@ IsZeroE e
            t ==@ BoolT
            infer gamma e (Val IntT)
       , do e <- var
            exp ==@ PredE e
            t ==@ IntT
            infer gamma e (Val IntT)
       , do e1 <- var
            e2 <- var
            exp ==@ MultE e1 e2
            t ==@ IntT
            infer gamma e1 (Val IntT)
            infer gamma e2 (Val IntT)
       , do e1 <- var
            e2 <- var
            e3 <- var
            exp ==@ IfE e1 e2 e3
            infer gamma e1 (Val BoolT)
            infer gamma e2 t
            infer gamma e3 t
       , do x <- var
            body <- var
            t1 <- var
            t2 <- var
            t ==@ FunT t1 t2
            exp ==@ LamE x body
            infer (Val (Cons (Val (x, t1)) gamma)) body t2
       , do rator <- var
            rand <- var
            t1 <- var
            exp ==@ AppE rator rand
            infer gamma rator (Val (FunT t1 t))
            infer gamma rand t1
       ]

emptyG :: LogicVal TypEnv
emptyG = (Val Nil)

varE = Val . VarE . Val
intE = Val . IntE . Val
boolE = Val . BoolE . Val
isZeroE = Val . IsZeroE
predE = Val . PredE
multE x y = Val $ MultE x y
ifE t c a = Val $ IfE t c a
lamE x body = Val $ LamE (Val x) body
appE rator rand = Val $ AppE rator rand

testInt = do t <- var
             infer emptyG (intE 5) t
             return t

testIf = do t <- var
            infer emptyG (ifE (boolE True) (intE 2) (intE 3)) t
            return t

testIf2 = do t <- var
             infer emptyG (ifE (boolE True) (intE 2) (boolE False)) t
             return t

testLam = do t <- var
             infer emptyG (lamE "x" (intE 2)) t
             return t

testLam2 = do t <- var
              infer emptyG (lamE "x" (predE (varE "x"))) t
              return t