{-# LANGUAGE ExistentialQuantification #-}
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

newtype LogicVar a = LV { varId :: VarId } deriving (Eq, Ord)

instance Show (LogicVar a) where
  show _ = "<var>"

newtype WrappedVal = SV ()

instance Show WrappedVal where
  show _ = "<val>"

data SubstContents = SubstVar     VarId 
                   | SubstVal     WrappedVal 
                     deriving (Show)

type Subst = Map VarId SubstContents

emptyS :: Subst
emptyS = Map.empty

extendS :: LogicVar a -> LogicVal a -> Subst -> Subst
extendS (LV id)  (Val val)     s = Map.insert id (SubstVal (unsafeCoerce val)) s
extendS (LV id1) (Var (LV id2)) s = Map.insert id1 (SubstVar id2) s

data LogicVal a = Var (LogicVar a) | Val a
                deriving (Eq, Show)

walk :: LogicVal a -> Subst -> LogicVal a
walk (Val x) _ = Val x
walk (Var (LV id)) s = case Map.lookup id s of
                           Nothing -> Var (LV id)
                           Just (SubstVar id') -> walk (Var (LV id')) s
                           Just (SubstVal wrapped) -> Val (unsafeCoerce wrapped)
            
walk' :: LogicVar a -> Subst -> LogicVal a
walk' = walk . Var
       
x = LV 0 :: LogicVar Int
y = LV 1 :: LogicVar Int

s = extendS x (Var y) emptyS
s' = extendS y (Val 5) s

test = walk' x s'

class Unifiable a where
  unify :: a
        -> a
        -> Subst
        -> Maybe Subst

instance Eq a => Unifiable (LogicVal a) where
  unify x y s = 
    case (walk x s, walk y s) of
      (x', y') | x' == y' -> return s
      (Var var, y')      -> return $ extendS var y' s
      (x', Var var)      -> return $ extendS var x' s
      _                   -> mzero

instance (Eq a, Unifiable a) => Unifiable [a] where
  unify []     []     s = return s
  unify (x:xs) (y:ys) s = unify x y s >>= unify xs ys
  unify _      _      _ = mzero

type LogicState = (VarId, Subst)

emptyState :: LogicState
emptyState = (0, emptyS)

type LogicComp a = StateT LogicState [] a

var :: LogicComp (LogicVar a)
var = do id <- fst <$> get
         modify (\(id, s) -> (id+1, s))
         return $ LV id

(===) :: Unifiable a => a -> a -> LogicComp ()
x === y = do s <- snd <$> get
             case unify x y s of
               Nothing -> mzero
               Just s' -> modify (\(id, _) -> (id, s'))

($=$) :: (Eq a) => LogicVar a -> LogicVar a -> LogicComp ()
x $=$ y = Var x === Var y

($=@) :: (Eq a) => LogicVar a -> a -> LogicComp ()
x $=@ y = Var x === Val y

(@=$) :: (Eq a) => a -> LogicVar a -> LogicComp ()
(@=$) = flip ($=@)

(@=@) :: (Eq a) => a -> a -> LogicComp ()
x @=@ y = Val x === Val y

-- testComp :: LogicComp Int
testComp = do x <- var
              y <- var
              x $=$ y
              y $=@ 5
              return y

-- run :: LogicComp (LogicVar a) -> [Maybe a]
run c = map reifyOne results
  where results = runStateT c emptyState
        reifyOne (lv, (_, s)) = evalStateT (reify lv) emptyRS
           
testComp2 :: LogicComp (LogicVar Int)
testComp2 = do x <- var
               (x $=@ 5) `mplus` (x $=@ 6)
               return x

testComp3 = do x <- var
               x $=@ "foo"
--               x $=@ 5 -- program rejected with this uncommented!
               return x

testList = do x <- var
              y <- var
              x $=@ 5
              y $=@ [Val 1, Var x, Val 8]
              return y

data ReifiedVal a = ReiName VarId | ReiVal a

instance Show a => Show (ReifiedVal a) where
  show (ReiName id) = "_." ++ show id
  show (ReiVal x)   = show x

type ReifySubst = Map VarId VarId

emptyRS = Map.empty

type ReifyComp a = StateT ReifySubst (Reader Subst) a

class Reifiable a where
  reify :: LogicVar a -> (ReifyComp (ReifiedVal a))
  reify lv = do 
    s <- ask
    case walk' lv s of
      Val x -> return $ ReiVal x
      Var (LV id) -> do
        rs <- get
        case Map.lookup id rs of
          Just rname -> return $ ReiName rname
          Nothing -> do 
            let rname = fromIntegral $ Map.size rs
            modify (Map.insert id rname)
            return $ ReiName rname


instance Reifiable Integer

instance Reifiable a => Reifiable (LogicVal a)

--instance Reifiable a => Reifiable [a] where
--  reify lv s = undefined

-- instance Eq a => Reifiable (LogicVal a) where