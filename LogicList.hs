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
  unify xs ys = do
    s <- getSubst
    case (walk xs s, walk ys s) of
      (xs'            , ys'            ) | xs' == ys' -> return ()
      (Var id         , ys'            ) -> modifySubst (extendS (Var id) ys')
      (xs'            , Var id         ) -> modifySubst (extendS (Var id) xs')
      (Val (Cons x xs), Val (Cons y ys)) -> unify x y >> unify xs ys
      _                                  -> mzero

instance Reifiable a => Reifiable (LogicList (LogicVal a)) where
  reify lv = do
    s <- ask
    case walk lv s of
      Val Nil -> return $ Val Nil
      Val (Cons x xs) -> do
        x' <- reify x
        xs' <- reify xs
        return $ Val (Cons x' xs')
      Var id -> do
        rs <- get
        case Map.lookup id rs of
          Just rname -> return $ Var rname
          Nothing -> do 
            let rname = fromIntegral $ Map.size rs
            modify (Map.insert id rname)
            return $ Var rname

append :: Unifiable a
       => LogicVal (LogicList (LogicVal a))
       -> LogicVal (LogicList (LogicVal a))
       -> LogicVal (LogicList (LogicVal a))
       -> LogicComp ()
append xs ys out = 
  msum [ do xs  ==@ Nil
            out === ys
       , do x   <- var
            xs' <- var
            res <- var
            xs  ==@ Cons x xs'
            out ==@ Cons x res
            append xs' ys res
       ]

testAppend :: LogicComp (LogicVal (LogicList (LogicVal Int)))
testAppend = do x <- var
                y <- var
                z <- var
                x ==@ fromList (map Val [1..3])
                y ==@ fromList (map Val [4..6])
                append x y z
                return z

testAppend2 :: LogicComp (LogicVal (LogicList (LogicVal Int)))
testAppend2 = do x <- var
                 y <- var
                 z <- var
                 x ==@ fromList (map Val [1..3])
                 z ==@ fromList (map Val [1..6])
                 append x y z
                 return y

testLList = do x <- var
               y <- var
               fromList (map Val [(1 :: Integer)]) @=@ fromList [x]
               return x