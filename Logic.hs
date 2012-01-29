{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PackageImports #-}

module Logic where

import Control.Applicative
import Control.Monad
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import Unsafe.Coerce

type VarId = Integer

data LogicVal a = Var VarId | Val a
                deriving (Eq)

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
            
x = Var 0 :: LogicVal Int
y = Var 1 :: LogicVal Int

s = extendS x y emptyS
s' = extendS y (Val 5) s

test = walk x s'

class Unifiable a where
  unify :: a
        -> a
        -> Subst
        -> Maybe Subst

instance Unifiable Integer where
  unify x y s | x == y    = return s
              | otherwise = mzero

instance Eq a => Unifiable (LogicVal a) where
  unify x y s = 
    case (walk x s, walk y s) of
      (x', y') | x' == y' -> return s
      (Var id, y')        -> return $ extendS (Var id) y' s
      (x', Var id)        -> return $ extendS (Var id) x' s
      _                   -> mzero

instance (Eq a, Unifiable a) => Unifiable [a] where
  unify []     []     s = return s
  unify (x:xs) (y:ys) s = unify x y s >>= unify xs ys
  unify _      _      _ = mzero

type LogicState = (VarId, Subst)

emptyState :: LogicState
emptyState = (0, emptyS)

type LogicComp a = StateT LogicState [] a

var :: LogicComp (LogicVal a)
var = do id <- fst <$> get
         modify (\(id, s) -> (id+1, s))
         return $ Var id

(===) :: Unifiable a => a -> a -> LogicComp ()
x === y = do s <- snd <$> get
             case unify x y s of
               Nothing -> mzero
               Just s' -> modify (\(id, _) -> (id, s'))

(==@) :: (Eq a) => LogicVal a -> a -> LogicComp ()
x ==@ y = x === Val y

(@==) :: (Eq a) => a -> LogicVal a -> LogicComp ()
(@==) = flip (==@)

(@=@) :: (Eq a) => a -> a -> LogicComp ()
x @=@ y = Val x === Val y

-- testComp :: LogicComp Int
testComp = do x <- var
              y <- var
              x === y
              y ==@ 5
              return y

-- run :: LogicComp (LogicVar a) -> [Maybe a]
run c = map reifyOne results
  where results = runStateT c emptyState
        reifyOne (lv, (_, s)) = runReader (evalStateT (unRC $ reify lv) emptyRS) s
           
testComp2 :: LogicComp (LogicVal Int)
testComp2 = do x <- var
               (x ==@ 5) `mplus` (x ==@ 6)
               return x

testComp3 = do x <- var
               x ==@ "foo"
--               x ==@ 5 -- program rejected with this uncommented!
               return x

testList = do x <- var
              y <- var
              x ==@ 5
              y ==@ [Val 1, x, Val 8]
              return y

testList2 = do x <- var
               y <- var
               y ==@ [Val 1, x, Val 8]
               return y

testList3 = do x <- var
               y <- var
               z <- var
               x ==@ [Val 1, Val 2, z]
               y === x
               return y

type ReifySubst = Map VarId VarId

emptyRS = Map.empty

newtype ReifyComp a = RC { unRC :: StateT ReifySubst (Reader Subst) a }
    deriving (Functor, Monad, MonadReader Subst, MonadState ReifySubst)

class Reifiable a where
  reify :: LogicVal a -> (ReifyComp (LogicVal a))
  reify lv = do 
    s <- ask
    case walk lv s of
      Val x -> return $ Val x
      Var id -> do
        rs <- get
        case Map.lookup id rs of
          Just rname -> return $ Var rname
          Nothing -> do 
            let rname = fromIntegral $ Map.size rs
            modify (Map.insert id rname)
            return $ Var rname

instance Reifiable Char
instance Reifiable Int
instance Reifiable Integer

instance Reifiable a => Reifiable [LogicVal a] where
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

instance Reifiable a => Reifiable (LogicVal a)

--instance Reifiable a => Reifiable [a] where
--  reify lv s = undefined

-- instance Eq a => Reifiable (LogicVal a) where
