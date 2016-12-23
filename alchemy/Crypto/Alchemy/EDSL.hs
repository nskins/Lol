{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.EDSL where

import Crypto.Lol                      hiding (Pos (..))
import Crypto.Lol.Applications.SymmSHE

import Algebra.Additive as Additive (C)
import Algebra.Ring     as Ring (C)

import Data.Constraint
import Data.Type.Natural hiding ((:-), zero)

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b


-- | Lambda abstraction and application for leveled computations.

class LambdaD expr where
  -- | Abstract.
  lamD :: (expr da a -> expr db b) -> expr (da,db) (a -> b)

  -- | Apply.
  appD :: expr (da,db) (a -> b) -> expr da a -> expr db b


-- | Symantics for leveled plaintext operations of some depth @d@.

class SymPT expr where

  -- | Entailment of additive group structure.  (Addends must be at
  -- the same depth as output.)

  entailAdditiveSymPT :: (rp ~ Cyc t m zp)
                      => Tagged (expr d rp)
                         ((Additive rp) :- Additive (expr d rp))

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').

  -- CJP: generalize input depths?
  mulPT :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
           expr d rp -> expr d rp -> expr ('S d) rp


-- | Symantics for ciphertext operations.

class SymCT expr where

  -- | Entailment of ring structure.
  entailRingSymCT :: Tagged (expr ct)
                     ((Ring ct) :- Ring (expr ct))

  rescaleCT :: (RescaleCyc (Cyc t) zq' zq, ToSDCtx t m' zp zq') =>
               -- above constraints copied from rescaleLinearCT
               expr (CT m zp (Cyc t m' zq')) -> expr (CT m zp (Cyc t m' zq))



-- | Metacircular evaluator.
newtype I a = I { unI :: a }
  deriving (Eq, Show, Additive.C, Ring.C)

-- | Metacircular lambda.
instance Lambda I where
  lam f   = I $ unI . f . I
  app f a = I $ unI f $ unI a

-- | Metacircular ciphertext symantics.
instance SymCT I where
  entailRingSymCT = tag $ Sub Dict
  rescaleCT = I . rescaleLinearCT . unI



-- | Metacircular evaluator with depth.
newtype ID d a = ID { unID :: a }
  deriving (Eq, Show, Additive.C, Ring.C)

-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f $ unID a

-- | Metacircular plaintext symantics.
instance SymPT ID where
  entailAdditiveSymPT = tag $ Sub Dict
  mulPT a b = ID $ unID a * unID b


-- | Encodes a sequence of @Z_q@ types, with needed constraints, for
-- depth-@d@ computations. (The exposed type @zq@ is the one used at
-- depth @d@.)
data Zqs t zp d zq where
  ZqZ :: (Encode zq zp) => Zqs t zp 'Z zq

  ZqS :: (RescaleCyc (Cyc t) zq' zq,
          Encode zp zq', CElt t zq') -- ToSDCtx minus Fact m'
      => Zqs t zp d zq' -> Zqs t zp ('S d) zq


-- CJP: make sure all the constraints in the GADT, functions, and
-- instances below make logical sense.  Some are weird and I don't
-- yet see whether there are better alternatives.


-- | Plaintext to ciphertext compiler.
data PT2CT              -- GHC wants complete kind signature for polymorphism
  (ctexpr :: * -> *)    -- ^ symantics of target ciphertext expression
  (m' :: Factored)      -- ^ ciphertext index (move to function arg?)
  (d :: k)              -- ^ depth of computation
  (a :: *)              -- ^ type of the plaintext expression
  where
    P2CTerm  :: (m `Divides` m', Eq zp) => -- Eq to get Ring for CT over Rq
                (forall zq ct . (ct ~ CT m zp (Cyc t m' zq), Ring ct) =>
                 Zqs t zp d zq -> ctexpr ct)
             -> PT2CT ctexpr m' d (Cyc t m zp)

    P2CLam :: (PT2CT ctexpr m' d a -> PT2CT ctexpr m' d b)
           -> PT2CT ctexpr m' (da,db) (a -> b)

-- CJP: want a conversion that works for both Term and Lam.  How to
-- write the type signature for it?

-- | Convert from 'SymPT' to 'SymCT' (using 'PT2CT').
pt2CT :: (ct ~ CT m zp (Cyc t m' zq), Ring ct)
      => PT2CT ctexpr m' d (Cyc t m zp)
      -> Zqs t zp d zq
      -> ctexpr (CT m zp (Cyc t m' zq))
pt2CT (P2CTerm f) zqs = f zqs

instance (SymCT ctexpr, rp ~ Cyc t m zp)
  => Additive.C (PT2CT ctexpr m' d rp) where

  -- zero = P2CTerm (\zqs -> zero \\ witness entailRingSymCT zero)

  (P2CTerm a) + (P2CTerm b) = P2CTerm (\zqs -> (a zqs) + (b zqs)
                                        \\ witness entailRingSymCT (a zqs))

  negate (P2CTerm a) = P2CTerm (\zqs -> negate (a zqs)
                                 \\ witness entailRingSymCT (a zqs))

instance (SymCT ctexpr) => SymPT (PT2CT ctexpr m') where
  entailAdditiveSymPT = tag $ Sub Dict

  -- still needs keyswitch
  mulPT (P2CTerm a) (P2CTerm b) =
    P2CTerm (\(ZqS zqs) -> let a' = rescaleCT (a zqs)
                               b' = rescaleCT (b zqs)
                           in a' * b' \\ witness entailRingSymCT a')
