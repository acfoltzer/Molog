{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PackageImports #-}

module Language.Logic.LogicList where

import Language.Logic

import Control.Applicative
import Control.Monad hiding (mapM)
import "mtl" Control.Monad.Reader hiding (mapM)
import "mtl" Control.Monad.State  hiding (mapM)

import Data.Map (Map)
import qualified Data.Map as Map

import Prelude hiding (mapM)

data LogicList a = Nil
                 | Cons (LogicVal a) (LogicVal (LogicList a))
                   deriving (Eq, Show)

instance Functor LogicList where
  fmap _ Nil                  = Nil
  fmap f (Cons hd tl) = Cons (f <$> hd) ((fmap f) <$> tl)

fromList :: [a] -> LogicList a
fromList []     = Nil
fromList (x:xs) = Cons (Val x) (Val $ fromList xs)

toList :: LogicList a -> Maybe [a]
toList Nil                     = return []
toList (Cons (Val x) (Val xs)) = (:) x <$> toList xs
toList _                       = mzero

mapM :: Monad m => (a -> m b) -> LogicList a -> m (LogicList b)
mapM _ Nil       = return Nil
mapM f (Cons x xs) = do 
  v <- case x of
         Var id -> return $ Var id
         Val x  -> do v <- f x; return $ Val v
  case xs of
    Var id -> return $ Cons v (Var id)
    Val xs -> do vs <- mapM f xs
                 return $ Cons v (Val vs)

instance Unifiable a => Unifiable (LogicList a) where
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
      Var id -> reifyVar (Var id)

append :: Unifiable a
       => LogicVal (LogicList a)
       -> LogicVal (LogicList a)
       -> LogicVal (LogicList a)
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

testAppend :: LogicComp (LogicVal (LogicList Int))
testAppend = do x <- var
                y <- var
                z <- var
                x ==@ fromList [1..3]
                y ==@ fromList [4..6]
                append x y z
                return z

testAppend2 :: LogicComp (LogicVal (LogicList Int))
testAppend2 = do x <- var
                 y <- var
                 z <- var
                 x ==@ fromList [1..3]
                 z ==@ fromList [1..6]
                 append x y z
                 return y

testLList :: LogicComp (LogicVal Integer)
testLList = do x <- var
               y <- var
               fromList [1] @=@ Cons x (Val Nil)
               return x