{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}

module Crypto.Alchemy.EDSL where

-- import Data.Typeable

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE
import Crypto.Lol.Cyclotomic.Tensor    (Tensor)

class Lambda rep where
  lam :: (rep a -> rep b) -> rep (a -> b)
  app :: rep (a -> b) -> rep a -> rep b

-- | Symantics for plaintext operations.

class SymPT rep where
  litPT :: (rp ~ (Cyc t m zp), Tensor t, Fact m) => rep rp

  addPT, mulPT :: (rp ~ (Cyc t m zp), Tensor t, Fact m) =>
                  rep rp -> rep rp -> rep rp


-- | Symantics for ciphertext operations
class SymCT rep where
  -- CJP: would be nice to enforce that rep ct is Additive, Ring, but
  -- this would seem to require entailment
  addCT, mulCT :: (ct ~ CT m zp (Cyc t m' zq),
                   Eq zp, m `Divides` m', ToSDCtx t m' zp zq) =>
                  rep ct -> rep ct -> rep ct

  rescaleCT :: (RescaleCyc (Cyc t) zq zq', ToSDCtx t m' zp zq) =>
               rep (CT m zp (Cyc t m' zq)) -> rep (CT m zp (Cyc t m' zq'))

  ksQuadCirc :: (ct ~ CT m zp (Cyc t m' zq),
                 KeySwitchCtx gad t m' zp zq zq') =>
                KSQuadCircHint gad (Cyc t m' zq') -> rep ct -> rep ct




{- OLD STUFF, HOPEFULLY NOT NEEDED -}

{-

-- | (nested) list of type representations for a list of types
data Ctx :: * -> * where
  CtxZ :: Ctx ()
  CtxS :: Typeable a => Ctx ctx -> Ctx (a, ctx)

-- | Peano representation of the position of a distinguished type in a
-- (nested) type list
data Index :: * -> * -> * where
  IndexZ :: Index (a, ctx) a
  IndexS :: Index ctx a -> Index (b, ctx) a

ctxLen :: Ctx a -> Int
ctxLen CtxZ = 0
ctxLen (CtxS ctx) = 1 + ctxLen ctx

tshift' :: Int -> Ctx j -> Ctx (a, i) -> Index j a
tshift' _ CtxZ _ = error "tshift': impossible!"
tshift' 0 (CtxS _) (CtxS _) = IndexZ
tshift' n (CtxS c1) c2 = IndexS (tshift' (n-1) c1 c2)

tshift :: Ctx j -> Ctx (a, i) -> Index j a
tshift c1 c2 = tshift' (ctxLen c1 - ctxLen c2) c1 c2

-- | Plaintext expression (in de Bruijn form), parameterized by
-- (nested) list of types of the free variables, and type of the term
-- itself.
data PTTerm :: * -> * -> * where
  -- | plaintext literal
  PTLit :: (a ~ Cyc t m r, Tensor t, Fact m) =>
           a -> PTTerm ctx a

  -- | plaintext addition
  PTAdd :: (a ~ Cyc t m r, Tensor t, Fact m) =>
           PTTerm ctx a -> PTTerm ctx a -> PTTerm ctx a

  -- | plaintext multiplication
  PTMul :: (a ~ Cyc t m r, Tensor t, Fact m) =>
           PTTerm ctx a -> PTTerm ctx a -> PTTerm ctx a

  -- | plaintext variable
  PTVar :: Typeable a => Index ctx a -> PTTerm ctx a

  -- | lambda
  PTLam :: (Typeable a, Typeable b) =>
           PTTerm (a, ctx) b -> PTTerm ctx (a -> b)

  -- | apply lambda
  PTApp :: (Typeable a, Typeable b) =>
           PTTerm ctx (a -> b) -> PTTerm ctx a -> PTTerm ctx b

-- | typed de Bruijn term
newtype PTT a = PTT { unPTT :: forall ctx . Ctx ctx -> PTTerm ctx a }

-}
