{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PackageImports #-}

module LogicList where

import Logic

import Control.Applicative
import Control.Monad hiding (mapM)
import "mtl" Control.Monad.Reader hiding (mapM)
import "mtl" Control.Monad.State  hiding (mapM)

import Data.Map (Map)
import qualified Data.Map as Map

import Prelude hiding (mapM)

data LogicList a = Nil
                 | Cons a (LogicVal (LogicList a))
                   deriving (Eq, Show)

instance Functor LogicList where
  fmap _ Nil               = Nil
  fmap f (Cons x (Var id)) = Cons (f x) (Var id)
  fmap f (Cons x (Val xs)) = Cons (f x) (Val (fmap f xs))

fromList :: [a] -> LogicList a
fromList []     = Nil
fromList (x:xs) = Cons x (Val $ fromList xs)

mapM :: Monad m => (a -> m b) -> LogicList a -> m (LogicList b)
mapM _ Nil       = return Nil
mapM f (Cons x xs) = do 
  v <- f x
  case xs of
    Var id -> return $ Cons v (Var id)
    Val xs -> do vs <- mapM f xs
                 return $ Cons v (Val vs)

instance (Eq a, Unifiable a) => Unifiable (LogicList (LogicVal a)) where
  unify Nil         Nil         s = return s
  unify (Cons x xs) (Cons y ys) s = unify x y s >>= unify xs ys
  unify _           _           _ = mzero


instance Reifiable a => Reifiable (LogicList (LogicVal a)) where
  reify lv = do
    s <- ask
    case walk lv s of
      Val xs -> Val <$> mapM reify xs
      Var id -> do
        rs <- get
        case Map.lookup id rs of
          Just rname -> return $ Var rname
          Nothing -> do 
            let rname = fromIntegral $ Map.size rs
            modify (Map.insert id rname)
            return $ Var rname

append :: Eq a
       => LogicVal (LogicList a)
       -> LogicVal (LogicList a)
       -> LogicVal (LogicList a)
       -> LogicComp ()
append xs ys out = 
  msum [ do xs  ==@ Nil
            out ==@ Nil
       , do x   <- var
            xs' <- var
            res <- var
            xs  ==@ Cons x xs'
            out ==@ Cons x res
            append xs' ys res
       ]
            
testAppend = do x <- var
                y <- var
                z <- var
                x ==@ fromList (map Val [1,2,3])
                y ==@ fromList (map Val [4,5,6])
                append x y z
                return z

testLList = do x <- var
               y <- var
               fromList (map Val [(1 :: Integer)]) === fromList [x]
               return x