{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PackageImports #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Language.Logic where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import Unsafe.Coerce

import Text.Printf
import qualified Debug.Trace as DT

type VarId = Integer

data LogicVal a = Var VarId | Val a
                deriving (Eq)

instance Functor LogicVal where
  fmap f (Var id) = Var id
  fmap f (Val x)  = Val (f x)

instance Show a => Show (LogicVal a) where
  show (Var id) = "_." ++ show id
  show (Val x)  = show x

data WrappedVal

instance Show WrappedVal where
  show _ = "<val>"

data SubstContents = SubstVar VarId 
                   | SubstVal WrappedVal 
                     deriving (Show)

type Subst = Map VarId SubstContents

emptyS :: Subst
emptyS = Map.empty

extendS :: LogicVal a -> LogicVal a -> Subst -> Subst
extendS (Var id)  (Val val) s = Map.insert id (SubstVal (unsafeCoerce val)) s
extendS (Var id1) (Var id2) s = Map.insert id1 (SubstVar id2) s
extendS _         _         _ = error "cannot extend subst with a value"

walk :: LogicVal a -> Subst -> LogicVal a
walk (Val x) _ = Val x
walk (Var id) s = case Map.lookup id s of
                    Nothing -> Var id
                    Just (SubstVar id') -> walk (Var id') s
                    Just (SubstVal wrapped) -> Val (unsafeCoerce wrapped)
            
testx = Var 0 :: LogicVal Int
testy = Var 1 :: LogicVal Int

tests = extendS testx testy emptyS
tests' = extendS testy (Val 5) tests

testWalk = walk testx tests'

getSubst :: LogicComp Subst
getSubst = snd <$> get

modifySubst :: (Subst -> Subst) -> LogicComp ()
modifySubst f = modify (\(varId, s) -> (varId, f s))

class Eq a => Unifiable a where
  unify :: LogicVal a
        -> LogicVal a
        -> LogicComp ()
  unify x y = do
    s <- getSubst
    case (walk x s, walk y s) of
      (x'    , y'    ) | x' == y' -> return ()
      (Var id, y'    ) -> modifySubst (extendS (Var id) y')
      (x'    , Var id) -> modifySubst (extendS (Var id) x')
      _                -> mzero

instance Unifiable Bool
instance Unifiable Int
instance Unifiable Integer
instance Unifiable Char

instance Unifiable a => Unifiable [a] where
  unify xs ys = do
    s <- getSubst
    case (walk xs s, walk ys s) of
      (xs'   , ys'   ) | xs' == ys' -> return ()
      (Var id, ys'   ) -> modifySubst (extendS (Var id) ys')
      (xs'   , Var id) -> modifySubst (extendS (Var id) xs')
      _                -> mzero

instance (Unifiable a) => Unifiable [LogicVal a] where
  unify xs ys = do
    s <- getSubst
    case (walk xs s, walk ys s) of
      (xs'     , ys'     ) | xs' == ys' -> return ()
      (Var id  , ys'     ) -> modifySubst (extendS (Var id) ys')
      (xs'     , Var id  ) -> modifySubst (extendS (Var id) xs')
      ((Val xs), (Val ys)) -> zipWithM_' unify xs ys
        where zipWithM_' f []     []     = return ()
              zipWithM_' f (x:xs) (y:ys) = f x y >> zipWithM_' f xs ys
              zipWithM_' f _      _      = mzero

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where
  unify x y = do
    s <- getSubst
    case (walk x s, walk y s) of
      (x', y') | x' == y' -> return ()
      (Var id, y') -> modifySubst (extendS (Var id) y')
      (x', Var id) -> modifySubst (extendS (Var id) x')
      _            -> mzero

instance (Unifiable a, Unifiable b) => Unifiable (LogicVal a, LogicVal b) where
  unify x y = do
    s <- getSubst
    case (walk x s, walk y s) of
      (x', y') | x' == y' -> return ()
      (Var id, y') -> modifySubst (extendS (Var id) y')
      (x', Var id) -> modifySubst (extendS (Var id) x')
      (Val (xf, xs), Val (yf, ys)) -> unify xf yf >> unify xs ys

type LogicState = (VarId, Subst)

emptyState :: LogicState
emptyState = (0, emptyS)

type LogicComp a = StateT LogicState Logic a

var :: LogicComp (LogicVal a)
var = do id <- fst <$> get
         modify (\(id, s) -> (id+1, s))
         return $ Var id

(===) :: Unifiable a => LogicVal a -> LogicVal a -> LogicComp ()
(===) = unify

(==@) :: (Unifiable a) => LogicVal a -> a -> LogicComp ()
x ==@ y = x === Val y

(@==) :: (Unifiable a) => a -> LogicVal a -> LogicComp ()
(@==) = flip (==@)

(@=@) :: (Unifiable a) => a -> a -> LogicComp ()
x @=@ y = Val x === Val y

testComp :: LogicComp (LogicVal Int)
testComp = do x <- var
              y <- var
              x === y
              y ==@ 5
              return y

run :: Reifiable a => LogicComp (LogicVal a) -> [LogicVal a]
run c = map reifyOne results
  where results = observeAll $ runStateT c emptyState
        reifyOne (lv, (_, s)) = 
          runReader (evalStateT (unRC $ reify lv) emptyRS) s          

testComp2 :: LogicComp (LogicVal Int)
testComp2 = do x <- var
               (x ==@ 5) `mplus` (x ==@ 6)
               return x

testComp3 :: LogicComp (LogicVal String)
testComp3 = do x <- var
               x ==@ "foo"
--               x ==@ 5 -- program rejected with this uncommented!
               return x

testList :: LogicComp (LogicVal [LogicVal Int])
testList = do x <- var
              y <- var
              x ==@ 5
              y ==@ [Val 1, x, Val 8]
              return y

testList2 :: LogicComp (LogicVal [LogicVal Int])
testList2 = do x <- var
               y <- var
               y ==@ [Val 1, x, Val 8]
               return y

testList3 :: LogicComp (LogicVal [LogicVal Int])
testList3 = do x <- var
               y <- var
               z <- var
               x ==@ [Val 1, Val 2, z]
               y === x
               return y

type ReifySubst = Map VarId VarId

emptyRS = Map.empty

newtype ReifyComp a = RC { unRC :: StateT ReifySubst (Reader Subst) a }
    deriving (Functor, Applicative, Monad, MonadReader Subst, MonadState ReifySubst)

class Reifiable a where
  reify :: LogicVal a -> (ReifyComp (LogicVal a))
  reify lv = do 
    s <- ask
    case walk lv s of
      Val x -> return $ Val x
      Var id -> reifyVar (Var id)

instance Reifiable Bool
instance Reifiable Char
instance Reifiable Int
instance Reifiable Integer
instance Reifiable [a]

instance Reifiable a => Reifiable [LogicVal a] where
  reify lv = do
    s <- ask
    case walk lv s of
      Val xs -> Val <$> mapM reify xs
      Var id -> reifyVar (Var id)

instance Reifiable a => Reifiable (LogicVal a)

reifyVar :: LogicVal a -> ReifyComp (LogicVal a)
reifyVar (Var id) = do
  rs <- get
  case Map.lookup id rs of
    Just rname -> return $ Var rname
    Nothing -> do 
      let rname = fromIntegral $ Map.size rs
      modify (Map.insert id rname)
      return $ Var rname
reifyVar _ = error "reifyVar is only for fresh variables"                        

--instance Reifiable a => Reifiable [a] where
--  reify lv s = undefined

-- instance Eq a => Reifiable (LogicVal a) where
