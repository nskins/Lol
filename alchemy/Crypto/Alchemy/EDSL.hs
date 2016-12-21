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

import Data.Type.Natural as Nat


class Lambda expr where
  -- | Abstract a Haskell function.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b

-- | Lambda annotated by depth in its argument.
newtype LamD (d :: Nat) a b = LamD { unLamD :: (a -> b) }

applyD :: LamD d a b -> a -> b
applyD = ($) . unLamD



-- | Depth-annotated lambda abstraction and application.
class LambdaD expr where
  -- | Abstract a function.
  lamD :: (LamD d (expr a) (expr b)) -> expr (LamD d a b)

  -- | Apply an abstraction.
  appD :: expr (LamD d a b) -> expr a -> expr b


-- | Symantics for plaintext operations, associated with
-- multiplicative depth.

class SymPT expr where

  addPT :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
           -- rp -> rp -> rp, depth 0 in both args
           LamD N0 (expr rp) (LamD N0 (expr rp) (expr rp))

  mulPT :: (rp ~ Cyc t m zp, Fact m, CElt t zp) =>
           -- rp -> rp -> rp, depth 1 in both args
           LamD N1 (expr rp) (LamD N1 (expr rp) (expr rp))

-- | Symantics for ciphertext operations

-- CJP: should this be associated with mult depth as well?  Not clear
-- that we need it anymore.
class SymCT expr where

  addCT, mulCT :: (ct ~ CT m zp (Cyc t m' zq))
                  => expr ct -> expr ct -> expr ct



-- | Metacircular evaluator.
newtype I a = I { unI :: a }

instance Lambda I where
  lam f   = I $ unI . f . I
  app f a = I $ (unI f) (unI a)

-- | Metacircular lambda abstraction and application.
instance LambdaD I where
  lamD f   = I $ unI . f . I
  appD f a = I $ f a

-- | Metacircular ring operations.
instance SymPT I where
  addPT = LamD (\a -> LamD (\b -> a + b))
  mulPT = LamD (\a -> LamD (\b -> a * b))


-- CJP: already defined somewhere?
type family Drop (d :: Nat) (xs :: [k]) where
  Drop 'Z xs = xs
  Drop ('S d) (x ': rest) = Drop d rest

-- | The type of a ciphertext expression corresponding to a
-- depth-annotated plaintext expression.

type family PT2CT (m' :: Factored) (zqs :: [*]) (d :: Nat) a where
  PT2CT m' (zq ': _) d (Cyc t m zp) = CT m zp (Cyc t m' zq)

  -- CJP: the 'Z here is arbitrary, and is likely wrong...
  PT2CT m' zqs l (a -> b) = PT2CT m' (Drop l zqs) 'Z a -> PT2CT m' zqs l b


-- | Plaintext to ciphertext compiler.
newtype C
  ctexpr -- ^ symantics of target ciphertext expression
  m'     -- ^ ciphertext index
  zqs    -- ^ typelist of (increasing) ciphertext moduli (head is root)
  d      -- ^ depth of the plaintext expression
  a      -- ^ type of the plaintext expression
  = C (ctexpr (PT2CT m' zqs d a))

