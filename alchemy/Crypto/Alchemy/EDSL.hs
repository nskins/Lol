{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.EDSL where

import Crypto.Lol
-- why doesn't Lol export Tensor type?
import Crypto.Lol.Cyclotomic.Tensor

import Data.Constraint

class Lambda expr where
  lam :: (expr a -> expr b) -> expr (a -> b)
  app :: expr (a -> b) -> expr a -> expr b

-- CJP: design question: do we go with stronger single-argument
-- SymPT/CT classes, which support very general methods that must work
-- for all m, m' etc., subject to constraints?  It then becomes a bit
-- tricky to know what constraints are appropriate for arbitrary
-- instances.  (We could define them on a per-instance basis as
-- associated types, but this is uuuuugly.)
--
-- Or do we go with weaker classes that include m, m' etc. as
-- arguments?  This makes it harder/impossible to define methods that
-- "switch arguments" (like moduli).  One would have to define
-- multiple classes that had all relevant arguments as parameters.


-- | Symantics for plaintext operations.

class SymPT (expr :: Factored -> * -> *) where
  type SymPTElt expr zp :: Constraint -- yuck, but necessary?

  -- type PTOf expr (m :: Factored) zp :: *

  -- litPT :: PTOf expr m zp -> expr m zp

  -- CJP: might be nicer to get these via entailment
  addPT, mulPT :: (Fact m, SymPTElt expr zp) =>
                  expr m zp -> expr m zp -> expr m zp

-- | Symantics for ciphertext operations
class SymCT expr where

  -- CJP: entailment?
  addCT, mulCT :: (e ~ expr m' zq m zp, m `Divides` m') =>
                  e -> e -> e

  {- How to handle RescaleCyc constraint? Associated constraint type instead?
  rescaleCT :: (RescaleCyc (Cyc t) zq zq') =>
               expr m zp m' zq -> expr m zp m' zq'

  ksQuadCirc :: (ct ~ expr m zp m' zq,
                 KeySwitchCtx gad t m' zp zq zq') =>
                KSQuadCircHint gad (Cyc t m' zq') -> ct -> ct
  -}


-- | Metacircular evaluator (analogous to identity monad).
newtype I a = I { unI :: a }

-- | Metacircular lambda abstraction and application.
instance Lambda I where
  lam f = I $ unI . f . I
  app (I f) (I a) = I $ f a


-- | Naive plaintext evaluator.
newtype EvalPT t m zp = EPT { unEPT :: Cyc t m zp }

instance (Tensor t) => SymPT (EvalPT t) where
  type SymPTElt (EvalPT t) zp = CElt t zp

  addPT (EPT a) (EPT b) = EPT $ a + b
  mulPT (EPT a) (EPT b) = EPT $ a * b

-- PROBLEM! Can't make EvalPT or (EvaltPT t) a meaningful instance of
-- Lambda because the kinds don't meaningfully match up

-- | Plaintext-to-ciphertext transformer.
data PT2CT expr (m' :: Factored) zq (m :: Factored) zp where
  P2C :: (m `Divides` m') => expr m' zq m zp -> PT2CT expr m' zq m zp

instance SymCT expr => SymPT (PT2CT expr m' zq) where
  type SymPTElt (PT2CT expr m' zq) zp = () -- nothing needed?

  addPT (P2C a) (P2C b) = P2C $ addCT a b
  mulPT (P2C a) (P2C b) = P2C $ mulCT a b

