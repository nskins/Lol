{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.EDSL where

import Crypto.Lol                      hiding (Pos (..))
import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Types

-- not using TypeLits because they don't seem to be a good fit (no
-- Peano rep)

--import Data.Promotion.Prelude
--import Data.Singletons.TypeLits

import Data.Type.Natural

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b


data Level (l :: Nat) a = L { unL :: a }


-- | Lambda abstraction and application for leveled computations.

class LambdaL expr where
  -- | Abstract a Haskell function that takes a leveled input.
  lamL :: (expr (Level l a) -> expr b) -> expr (Level l a -> b)

  -- | Apply an abstraction.
  appL :: expr (Level l a -> b) -> expr (Level l a) -> expr b


-- | Symantics for leveled plaintext operations.

class SymPT expr where

  -- | Plaintext addition.  Inputs must be at the same level as
  -- outputs.
  addPT :: ( -- (l :<= l1) ~ 'True, (l :<= l2) ~ 'True,
           -- CJP: generalize input levels?
            rp ~ Cyc t m zp, Fact m, CElt t zp) =>
           expr (Level l rp) -> expr (Level l rp) -> expr (Level l rp)

  -- | Plaintext multiplication.  Inputs must be one level higher than
  -- output.
  mulPT :: ( -- (l :< l1) ~ 'True, (l :< l2) ~ 'True,
           -- CJP: generalize input levels?
            rp ~ Cyc t m zp, Fact m, CElt t zp) =>
           expr (Level ('S l) rp) -> expr (Level ('S l) rp) -> expr (Level l rp)


-- CJP: should the following be leveled as well?  Don't think we need
-- it here.

-- | Symantics for ciphertext operations

class SymCT expr where

  addCT, mulCT :: (ct ~ CT m zp (Cyc t m' zq)) =>
                  expr ct -> expr ct -> expr ct

  rescaleCT :: (RescaleCyc (Cyc t) (a,b) b, ToSDCtx t m' zp (a,b)) =>
               expr (CT m zp (Cyc t m' (a,b))) -> expr (CT m zp (Cyc t m' b))

-- | Metacircular evaluator.
newtype I a = I { unI :: a }

-- | Metacircular lambda abstraction and application.
instance Lambda I where
  lam f   = I $ unI . f . I
  app f a = I $ unI f (unI a)

-- | Metacircular lambda abstraction and application.
instance LambdaL I where
  lamL f   = I $ unI . f . I
  appL f a = I $ unI f (unI a)

unIL :: I (Level l a) -> a
unIL = unL . unI

-- | Metacircular ring operations.
instance SymPT I where
  addPT a b = I $ L $ unIL a + unIL b
  mulPT a b = I $ L $ unIL a * unIL b

-- | Collect the first @n+1@ moduli into a /reverse/ nested pair of
-- 'ZqBasic's, representing a product ring.  (Reverse because we want
-- to strip off the first element of an @n@-tuple to get the
-- @(n-1)@-tuple.)
type family ZqProd n qs where
  ZqProd 'Z     qs = (ZqBasic (Elt 'Z qs) Int64)
  ZqProd ('S n) qs = (ZqBasic (Elt  n qs) Int64, ZqProd n qs)

type family Elt n qs where
  Elt 'Z     (q ': _)  = q
  Elt ('S n) (_ ': qs) = Elt n qs

-- | Plaintext to ciphertext compiler.
data C
  ctexpr -- ^ symantics of target ciphertext expression
  m'     -- ^ ciphertext index
  qs     -- ^ typelist of individual moduli
  a      -- ^ type of the plaintext expression
  where
    CCT  :: ctexpr (CT m zp (Cyc t m' (ZqProd l qs)))
         -> C ctexpr m' qs (Level l (Cyc t m zp))
    CLam :: (C ctexpr m' qs a -> C ctexpr m' qs b)
         -> C ctexpr m' qs (a -> b)

instance (SymCT ctexpr) => SymPT (C ctexpr m' qs) where
  addPT (CCT a) (CCT b) = CCT $ addCT a b

  -- need keyswitch too
  mulPT (CCT a) (CCT b) = CCT $ mulCT (rescaleCT a) (rescaleCT b)
  -- CJP: somehow need to get (Reflects q Int64) constraints in scope
  -- here so we can get Unbox instances for (ZqBasic (Elt l qs) Int64)
  -- and/or (ZqProd l qs) ?
