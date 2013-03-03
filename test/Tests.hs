{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Monad

import Molog

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import Test.Framework.TH

main = $(defaultMainGenerator)

case_2vars = runMolog (reify =<< test) @=? [Just 5]
  where test :: Molog s (Term s Int)
        test  = do x <- fresh
                   y <- fresh
                   x `unify` (Val 5)
                   x `unify` y
                   return y

case_2vars_pair = runMolog (reify =<< test) @=? [Just (5, 5)]
  where test :: Molog s (Term s (Term s Int, Term s Int))
        test = do x <- fresh
                  y <- fresh
                  x `unify` (Val 5)
                  x `unify` y
                  p <- fresh
                  p `unify` (Val (x, y))
                  return p

case_disj = runMolog (reify =<< test) @=? [Just 5, Just 6]
  where test :: Molog s (Term s Int)
        test = do x <- fresh
                  msum [ x `unify` (Val 5)
                       , x `unify` (Val 5) >> x `unify` (Val 6)
                       , x `unify` (Val 6)
                       ]
                  return x

