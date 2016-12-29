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

  {- CJP: scrapping entailment here for the subtle reason that in the
 PT-to-CT compiler, the Additive instance for CT needs a weird extra
 constraint (namely, Eq zp) that shouldn't be exposed here.  But
 leaving it out makes it impossible to implement 'zero', and hence to
 construct the entailment.  Also, since we need a depth-aware
 multiplication operator, might as well have similar ones for
 addition/subtraction.

  -- | Entailment of additive group structure.  (Addends must be at
  -- the same depth as output.)

  entailAdditiveSymPT :: (rp ~ Cyc t m zp)
                      => Tagged (expr d rp)
                         ((Additive rp) :- Additive (expr d rp))
  -}


  (+#), (-#) :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
                -- CJP: generalize input depths?
                expr d rp -> expr d rp -> expr d rp

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').

  (*#) :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
          -- CJP: generalize input depths?
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
  a +# b = ID $ unID a + unID b
  a -# b = ID $ unID a - unID b
  a *# b = ID $ unID a * unID b


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
data PT2CT              -- GHC wants complete kind signature for polykindedness
  (ctexpr :: * -> *)    -- ^ symantics of target ciphertext expression
  (d :: k)              -- ^ depth of computation
  (a :: *)              -- ^ type of the plaintext expression
  :: *
  where
    P2CTerm  :: (Eq zp) =>      -- remove when SHE Additive CT instance fixed
                (forall proxy m' zq ct .
                 (m `Divides` m', ct ~ CT m zp (Cyc t m' zq),
                  Ring ct) => -- CJP: why Ring ct?  w/o it, weird compile errors
                  proxy m' -> Zqs t zp d zq -> ctexpr ct)
             -> PT2CT ctexpr d (Cyc t m zp)

    P2CLam :: (PT2CT ctexpr da a -> PT2CT ctexpr db b)
           -> PT2CT ctexpr (da,db) (a -> b)

-- CJP: want a conversion that works for both Term and Lam.  How to
-- write the type signature for it?

-- | Convert from 'SymPT' to 'SymCT' (using 'PT2CT').
pt2CT :: (m `Divides` m', ct ~ CT m zp (Cyc t m' zq), Ring ct)
      => PT2CT ctexpr d (Cyc t m zp)
      -> proxy m'
      -> Zqs t zp d zq
      -> ctexpr (CT m zp (Cyc t m' zq))
pt2CT (P2CTerm f) p zqs = f p zqs

instance (SymCT ctexpr) => SymPT (PT2CT ctexpr) where

  (P2CTerm a) +# (P2CTerm b) =
    P2CTerm (\p zqs -> let a' = a p zqs
                           b' = b p zqs
                       in a' + b' \\ witness entailRingSymCT a')

  (P2CTerm a) -# (P2CTerm b) =
    P2CTerm (\p zqs -> let a' = a p zqs
                           b' = b p zqs
                       in a' - b' \\ witness entailRingSymCT a')

  -- still needs keyswitch
  (P2CTerm a) *# (P2CTerm b) =
    P2CTerm (\p (ZqS zqs) -> let a' = rescaleCT (a p zqs)
                                 b' = rescaleCT (b p zqs)
                             in a' * b' \\ witness entailRingSymCT a')

instance LambdaD (PT2CT ctexpr) where
  lamD = P2CLam
  appD (P2CLam f) = f







{- CJP: vestigial from we had entailAdditiveSymPT
instance (SymCT ctexpr, Eq zp)
  => Additive.C (PT2CT ctexpr (d :: Nat) (Cyc t m zp)) where

  negate (P2CTerm a) = P2CTerm (\p zqs -> negate (a p zqs)
                                 \\ witness entailRingSymCT (a p zqs))
-}

