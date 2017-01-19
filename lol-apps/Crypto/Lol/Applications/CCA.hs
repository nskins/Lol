{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-} -- TODO: possibly unnecessary.
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- CCA.

-- TODO: determine which types/functions to export.
module Crypto.Lol.Applications.CCA
( decrypt,
  encrypt,
  genKeys,
  genMatrix,
  KeyPair
) where

import Control.Applicative hiding ((*>))
import Control.Monad
import Control.Monad.Random

import Crypto.Lol
import Crypto.Lol.Cyclotomic.Tensor (Tensor)
import Crypto.Lol.Types.FiniteField

import MathObj.Matrix as M

-- Set an appropriate value of lBar.
lBar :: Int
lBar = 5

-- | Represents the appropriate gadget as a matrix.
gadTM :: (Gadget gad u) => Tagged gad (Matrix u)
gadTM = do
  g <- gadget
  let k = length g
  return $ M.fromList 1 k g

-- | Secret key T.
type SK t m z = Matrix (Cyc t m z)
-- | Public key (v, [ aBar | aBar*T ]).
type PK t m z zq = (z, (Matrix (Cyc t m zq), Matrix (Cyc t m zq)))
-- | Secret key and public key pair.
type KeyPair t m z zq = (SK t m z, PK t m z zq)
-- | Plaintext.
type PT t m zp = Cyc t m zp
-- | Ciphertext.
type CT fp d t m zq = (GF fp d, (Matrix (Cyc t m zq), Matrix (Cyc t m zq)))

-- | Constraint synonym for generating the key pair.
type KeyGenCtx t m z zq gad =
        (CElt t z, CElt t zq, Fact m, Gadget gad zq, Random z,
        Random zq, Reduce z zq, ToInteger z)

-- | Generates the secret key and public key pair.
genKeys :: forall t m z zq gad rnd .
           (KeyGenCtx t m z zq gad, MonadRandom rnd) =>
           z -> TaggedT gad rnd (KeyPair t m z zq)
genKeys svar = do
  let k = untag $ length <$> (gadget :: Tagged gad [Cyc t m zq])
  aBar <- genMatrix 1 lBar getRandom -- row matrix.
  sk <- genMatrix lBar k (errorRounded svar)
  return $ (sk, (svar, (aBar, aBar * (reduce <$> sk) ) ) )

-- | Constraint synonym for encryption.
type EncryptCtx fp d t m zp zq gad =
        (CElt t (LiftOf zp), CElt t zp, CElt t zq, Fact m,
        Gadget gad zq, GFCtx fp d, Lift' zp, LiftOf zp ~ LiftOf zq,
        LiftOf zq ~ ModRep zp, Mod zp, Module (GF fp d) (Cyc t m zq),
        Random fp, Random (LiftOf zp), Reduce (LiftOf zp) zq)

-- | Encrypt the message.
encrypt :: forall fp d t m zp zq gad rnd .
           (EncryptCtx fp d t m zp zq gad, MonadRandom rnd) =>
           PK t m (LiftOf zp) zq -> PT t m zp ->
           TaggedT gad rnd (CT fp d t m zq)
encrypt (svar, (aBar, aBarT)) mu = do
  s <- tagT $ reduce <$> (errorRounded svar
            :: rnd (Cyc t m (LiftOf zp)))
  e1 <- errorCoset svar mu
  eBarRem <- replicateM (lBar-1) (errorRounded svar)
  let eBar = reduce <$> (M.fromList 1 lBar (e1 : eBarRem))
      k = untag $ length <$> (gadget
            :: Tagged gad [Cyc t m zq])
  ek <- tagT $ (fmap reduce) <$> (genMatrix 1 k (errorRounded svar)
            :: rnd (Matrix (Cyc t m (LiftOf zp))))
  v <- getRandom
  let gadM = untag $ (gadTM
            :: Tagged gad (Matrix (Cyc t m zq)))
  -- Note: av = (aBar, aBarT + v*>gadM), but we never actually need "av."
      b = ( (scale s aBar) + eBar,
            (scale s ( aBarT + ( (v*>) <$> gadM ) ) ) + ek)
  return (v, b)

-- | Constraint synonym for decryption.
type DecryptCtx fp d t m z zp zq gad =
        (CElt t z, CElt t zp, CElt t zq, Correct gad (Cyc t m zq),
        Fact m, Field (GF fp d), GFCtx fp d, Module (GF fp d) (Cyc t m zq),
        Reduce (Cyc t m z) (Cyc t m zq), Reduce (Cyc t m z) (Cyc t m zp),
        Lift zq z, Ord z)

-- | Decrypt the message.
decrypt :: (DecryptCtx fp d t m z zp zq gad) =>
           KeyPair t m z zq -> CT fp d t m zq ->
           Tagged gad (PT t m zp)
decrypt (sk, (svar, (aBar, aBarT))) (v, (bBar, bk)) = do
  let bHat = tag $ concat $ rows $ (bk - (bBar * (reduce <$> sk)))
  _ <- bHat
  let (sHat, _) = correct bHat
      s = (recip v) *> sHat
  gadM <- gadTM
  let e = (liftDec <$> (bBar - (scale s aBar)),
           liftDec <$> (bk - (scale s (aBarT + ((v*>) <$> gadM)))))
  if isShortVector svar e
  then return $ reduce (index (fst e) 0 0)
  else return $ reduce (index (fst e) 0 0) -- TODO: unknown.. what should 'else' return?

-- | Returns true if the cyclotomic ring element is short with
-- respect to the scaled variance parameter.
isShort :: (CElt t z, Fact m, Ord z) =>
         z -> (Cyc t m z) -> Bool
isShort svar = (<svar) . gSqNorm

-- | Returns true if every entry in the error vector is short with
-- respect to the scaled variance parameter.
isShortVector :: (CElt t z, Fact m, Ord z) => z ->
                 (Matrix (Cyc t m z), Matrix (Cyc t m z)) -> Bool
isShortVector svar (eBar, ek) =
  let ([l], [r]) = (rows eBar, rows ek)
  in (all (isShort svar) l) && (all (isShort svar) r)

-- | Generates a matrix with m rows and n columns.
-- Possible alg: getRandom, (errorRounded y), etc.
genMatrix :: (Tensor t, Fact m, Random z, MonadRandom rnd) =>
             Int -> Int -> rnd (Cyc t m z) -> rnd (Matrix (Cyc t m z))
genMatrix m n alg = do
  lists <- replicateM m (replicateM n alg)
  return $ M.fromRows m n lists
