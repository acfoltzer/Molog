{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Molog where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Ref
import Control.Monad.ST.Persistent

import Data.Maybe
import Data.STRef.Persistent

newtype Molog s a = M { unM :: STT s Logic a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus)

instance MonadRef (STRef s) (Molog s) where
  newRef       = M . newRef
  readRef      = M . readRef
  writeRef r x = M $ writeRef r x

data Term s a = Var !(STRef s (Maybe (Term s a)))
              | Val !a
                deriving (Eq, Show)

bindRef :: STRef s (Maybe (Term s a)) -> Term s a -> Molog s ()
bindRef r t = writeRef r (Just t)

semiprune :: Term s a -> Molog s (Term s a)
semiprune t@(Val _)   = return t
semiprune t@(Var ref) = go t ref
  where go t ref = do
          mt <- readRef ref
          case mt of
            -- fresh var: done
            Nothing            -> return t
            -- one pointer away: done
            Just (Val _)       -> return t
            -- do path compression
            Just t'@(Var ref') -> do
              result <- go t' ref'
              -- overwrite original pointer
              bindRef ref result
              return result

fresh :: Molog s (Term s a)
fresh = Var <$> newRef Nothing

class Unifiable s a where
  unify :: Term s a -> Term s a -> Molog s ()
  unifyWith :: (a -> a -> Molog s ()) -> Term s a -> Term s a -> Molog s ()

  default unify :: Eq a => Term s a -> Term s a -> Molog s ()
  unify x y = unifyWith guardEq x y
    where guardEq x y = guard (x == y)

  unifyWith f x y = do
    xt <- semiprune x
    yt <- semiprune y
    case (xt, yt) of
      (Var xr, Var yr) | xr == yr  -> return ()
                       | otherwise -> do
        mxt' <- readRef xr
        myt' <- readRef yr
        case (mxt', myt') of
          (Nothing, Nothing) -> bindRef xr yt
          (Nothing, Just _ ) -> bindRef xr yt
          (Just _ , Nothing) -> bindRef yr xt
          (Just (Val xv), Just (Val yv)) -> f xv yv
          _ -> error "impossible: more than 2 pointers after semiprune"
      (Var xr, Val yv) -> do
        mxt' <- readRef xr
        case mxt' of
          Nothing       -> bindRef xr yt
          Just (Val xv) -> f xv yv
          _ -> error "impossible: more than 2 pointers after semiprune"
      (Val xv, Var yr) -> do
        myt' <- readRef yr
        case myt' of
          Nothing       -> bindRef yr xt
          Just (Val yv) -> f xv yv
          _ -> error "impossible: more than 2 pointers after semiprune"
      (Val xv, Val yv) -> f xv yv


instance Unifiable s Int


instance (Unifiable s a, Unifiable s b) => Unifiable s (Term s a, Term s b) where
  unify x y = unifyWith unifyPairs x y
    where --unifyPairs :: (Term s a, Term s b) -> (Term s a, Term s b) -> Molog s ()
          unifyPairs (x1, y1) (x2, y2) = unify x1 x2 >> unify y1 y2

class Reifiable s a b | a -> b where
  reify :: a -> Molog s (Maybe b)

instance Reifiable s a b => Reifiable s (Term s a) b where
  reify (Val v) = reify v
  reify (Var ref) = do
    mt <- readRef ref
    case mt of
      Just (Val v)    -> reify v -- return . maybe Nothing (Just . Val) =<< reify v
      Just (Var ref') -> do
        mt' <- readRef ref'
        case mt' of
          Just (Val v) -> reify v
          _            -> return Nothing
      _ -> return Nothing

instance Reifiable s Int Int where
  reify = return . Just

instance (Reifiable s a c, Reifiable s b d) => Reifiable s (a, b) (c, d) where
  reify (x, y) = do
    mx' <- reify x
    my' <- reify y
    case (mx', my') of
      (Just x', Just y') -> return (Just (x', y'))
      _                  -> return Nothing

reify' :: Reifiable s a b => a -> Molog s b
reify' x = do mx' <- reify x
              case mx' of
                Nothing -> mzero
                Just x' -> return x'

runMolog :: (forall s . Molog s a) -> [a]
runMolog c = observeAll (runSTT (unM c))

{-

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
-}
