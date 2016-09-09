{-# LANGUAGE BangPatterns, ConstraintKinds, DataKinds, FlexibleContexts,
             FlexibleInstances, GADTs, GeneralizedNewtypeDeriving,
             KindSignatures, MultiParamTypeClasses, NoImplicitPrelude,
             PolyKinds, RankNTypes, RebindableSyntax, RoleAnnotations,
             ScopedTypeVariables, TypeOperators #-}

-- | A simple DSL for tensoring Repa arrays and other common functionality
-- on Repa arrays

module Crypto.Lol.Cyclotomic.Tensor.RepaTensor.RTCommon
( module R
, module Data.Array.Repa.Eval
, module Data.Array.Repa.Repr.Unboxed
, Arr(..), repl, replM, eval, evalM, fTensor, ppTensor
, Trans(Id), trans, (.*), (@*), force
, mulMat, mulDiag
, scalarPow'
, sumS, sumAllS
) where

import Crypto.Lol.Prelude as LP hiding ((!!))

import Algebra.Additive     as Additive (C)
import Algebra.Ring         as Ring (C)
import Algebra.ZeroTestable as ZeroTestable (C)

import Control.DeepSeq              (NFData (..))
import Control.Monad.Identity       ()
import Control.Monad.Random
import Data.Array.Repa              as R hiding (sumAllP, sumAllS, sumP,
                                          sumS, (*^), (+^), (-^), (/^))
import Data.Array.Repa.Eval         hiding (one, zero)
import Data.Array.Repa.Repr.Unboxed
import Data.Coerce
import Data.Singletons
import Data.Singletons.Prelude      hiding ((:.))
import Data.Vector.Unboxed          as U (replicate, replicateM)
import Test.QuickCheck

-- always unboxed (manifest); intermediate calculations can use
-- delayed arrays

-- | Indexed newtype for 1-dimensional Unbox repa arrays
newtype Arr (m :: Factored) r = Arr (Array U DIM1 r)
                              deriving (Eq, Show, NFData)

-- the first argument, though phantom, affects representation
-- CJP: why must the second arg be nominal?
-- EAC: From https://ghc.haskell.org/trac/ghc/wiki/Roles#Thesolution:
--   "The exception to the above algorithm is for classes: all parameters for a class default to a nominal role."
-- Arr is a synonym for Array, which is an associated data type to the class Source. The parameter `r` above
-- corresponds to the parameter `e` in the definition of class Source, so it's role must be nominal.
type role Arr nominal nominal

-- | An 'Arr' filled with the argument.
repl :: forall m r . (Fact m, Unbox r) => r -> Arr m r
repl = let n = proxy totientFact (Proxy::Proxy m)
       in Arr . fromUnboxed (Z:.n) . U.replicate n
{-# INLINABLE repl #-}

-- | Monadic version of 'repl'.
replM :: forall m r mon . (Fact m, Unbox r, Monad mon)
         => mon r -> mon (Arr m r)
replM = let n = proxy totientFact (Proxy::Proxy m)
        in fmap (Arr . fromUnboxed (Z:.n)) . U.replicateM n
{-# INLINABLE replM #-}

instance (Fact m, Additive r, Unbox r) => Additive.C (Arr m r) where
  zero = repl zero
  (Arr a) + (Arr b) = Arr $ force $ R.zipWith (+) a b
  negate (Arr a) = Arr $ force $ R.map negate a
  {-# INLINABLE zero #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE negate #-}

instance (Fact m, Ring r, Unbox r) => Ring.C (Arr m r) where
  one = repl one
  (Arr a) * (Arr b) = Arr $ force $ R.zipWith (*) a b
  fromInteger = repl . fromInteger
  {-# INLINABLE one #-}
  {-# INLINABLE (*) #-}
  {-# INLINABLE fromInteger #-}

instance (ZeroTestable r, Unbox r, Elt r) => ZeroTestable.C (Arr m r) where
  -- not using 'zero' to avoid Additive r constraint
  isZero (Arr a)
      = isZero $ foldAllS (\ x y -> if isZero x then y else x) (a R.! (Z:.0)) a
  {-# INLINABLE isZero #-}


instance (Unbox r) => NFData (Array U DIM1 r) where
  -- EAC: Repa doesn't define any NFData instances,
  -- I'm hoping deepSeqArray is a reasonable approx
  rnf x = deepSeqArray x ()

instance (Unbox r, Random r, Fact m) => Random (Arr m r) where
  random = runRand $ replM (liftRand random)

  randomR = error "randomR nonsensical for Arr"

instance (Arbitrary r, Unbox r, Fact m) => Arbitrary (Arr m r) where
    arbitrary = replM arbitrary
    shrink = shrinkNothing

-- | For a factored index, tensors up any function defined for (and
-- tagged by) any prime power
fTensor :: forall m r mon . (Fact m, Monad mon)
  => (forall pp . (PPow pp) => mon (Trans pp r))
  -> TaggedT mon (Trans m r)

fTensor func = tagT $ go $ sUnF (sing :: SFactored m)
  where
    go :: Sing (pplist :: [PrimePower]) -> mon (Trans m r)
    go spps = case spps of
          SNil -> return $ Id 1
          (SCons (spp :: Sing pp) rest) -> do
            rest' <- go rest
            func' :: Trans pp r <- func
            return $ rest' @* func'
{-# INLINABLE fTensor #-}

-- (Fact m, Fact m', PPow pp') => (Trans m' r) \otimes (Trans pp' r) :: Trans m r
-- (Bin b , Prime p, PPow pp) => (Trans b r) \otimes (Trans p r) :: Trans pp r
{-
-- | For a prime power p^e, tensors up any function f defined for
-- (and tagged by) a prime to @I_(p^{e-1}) \otimes f@
ppTensor :: forall pp r mon . (PPow pp, Monad mon)
            => (forall p . (Prime p) => TaggedT p mon (Trans r))
            -> TaggedT pp mon (Trans r)

ppTensor func = tagT $ case (sing :: SPrimePower pp) of
  pp@(SPP (STuple2 sp _)) -> do
    func' <- withWitnessT func sp
    let lts = withWitness valuePPow pp `div` withWitness valuePrime sp
    return $ Id lts @* func'
{-# INLINABLE ppTensor #-}
-}

-- deeply embedded DSL for transformations and their various
-- compositions

-- (dim(f), f) where f operates on innermost dimension of array
data TransC (l :: k) (m :: k) (r :: k) b = Tensorable !(Array D DIM2 b -> Array D DIM2 b)

-- transform component: a Tensorable with particular I_l, I_r
--type TransC l m r b = (Tensorable b, Int, Int)

-- full transform: sequence of zero or more components
-- | a DSL for tensor transforms on Repa arrays
data Trans (n :: k) b where
  Id :: Trans n b                                                            -- ^| identity sentinel
  TSnoc :: (l * m * r ~ n, Index m, Index r) => !(Trans n b) -> !(TransC l m r b) -> Trans n b -- ^| (function) composition of transforms

-- | smart constructor from a Tensorable
trans :: forall p b . (Fact p) => (Array D DIM2 b -> Array D DIM2 b) -> Trans p b
trans f = TSnoc Id (Tensorable f :: TransC F1 p F1 b) \\ coerceMulID (Proxy::Proxy p)
{-# INLINABLE trans #-}

-- | compose transforms
(.*) :: Trans m r -> Trans m r -> Trans m r
f .*  Id = f          -- drop sentinel
f .* (TSnoc rest g') = TSnoc (f .* rest) g'
{-# INLINABLE (.*) #-}

-- | tensor/Kronecker product (otimes)
(@*) :: forall n1 n2 b . (PPow n1, Fact n2) => Trans n1 b -> Trans n2 b -> Trans ((PpToF n1) * n2) b
-- merge identity transforms
Id @* Id = Id
-- Id on left or right
i@Id @* (TSnoc g' (g :: TransC l m r b)) = TSnoc (i @* g') (coerce g :: TransC ((PpToF n1)*l) m r b) \\ coerceMul (Proxy::Proxy l) (Proxy::Proxy m) (Proxy::Proxy r) (Proxy::Proxy (PpToF n1))
(TSnoc f' (f :: TransC l m r b)) @* i@Id = TSnoc (f' @* i) (coerce f :: TransC l m (r*n2) b) \\ coerceMul (Proxy::Proxy l) (Proxy::Proxy m) (Proxy::Proxy r) (Proxy::Proxy n2)
-- no Ids: compose
f @* g = (f @* (Id :: Trans n2 b)) .* ((Id :: Trans n1 b) @* g)
{-# INLINABLE (@*) #-}

evalC :: forall l m r b . (Unbox b, Index m, Index r) => TransC l m r b -> Array U DIM1 b -> Array U DIM1 b
evalC t@(Tensorable f) =
  let dim = proxy totient (Proxy :: Proxy m)
      r = proxy totient (Proxy::Proxy r)
  in force . unexpose r . f . expose dim r
{-# INLINABLE evalC #-}

-- | Creates an evaluatable Haskell function from a tensored transform
eval :: (Unbox r, Fact m) => Trans m r -> Arr m r -> Arr m r
eval = coerce . eval'
  where eval' :: (Unbox r, Fact m) => Trans m r -> Array U DIM1  r -> Array U DIM1 r
        eval' Id = id
        eval' (TSnoc rest f) = eval' rest . evalC f
{-# INLINABLE eval #-}

-- | Monadic version of 'eval'
evalM :: (Unbox r, Monad mon, Fact m) => mon (Trans m r) -> mon (Arr m r -> Arr m r)
evalM = fmap eval
{-# INLINE evalM #-}

-- | maps the innermost dimension to a 2-dim array with innermost dim d,
-- for performing a I_l \otimes f_d \otimes I_r transformation
expose :: (Source r1 r)
          => Int -> Int -> Array r1 DIM1 r -> Array D DIM2 r
expose !d !r !arr =
  let (Z :. sz) = extent arr
      f (Z :. i :. j) = let imodr = i `mod` r
                        in (Z :. (i-imodr)*d + j*r + imodr)
  in backpermute (Z :. sz `div` d :. d) f arr
{-# INLINABLE expose #-}

-- | inverse of expose
unexpose :: (Source r1 r) => Int -> Array r1 DIM2 r -> Array D DIM1 r
unexpose !r !arr =
  let (Z :. sz :. d) = extent arr
      f (Z :. i) = let (idivr,imodr) = i `divMod` r
                       (idivrd,j) = idivr `divMod` d
                   in (Z :. r*idivrd + imodr :. j)
  in backpermute (Z :. sz*d) f arr
{-# INLINABLE unexpose #-}

-- | general matrix multiplication along innermost dim of v
mulMat :: (Source r1 r, Source r2 r, Ring r, Unbox r, Elt r)
          => Array r1 DIM2 r -> Array r2 DIM2 r -> Array D DIM2 r
mulMat !m !v
  = let (Z :. mrows :. mcols) = extent m
        (sh :. vrows) = extent v
        f (sh' :. i) = sumAllS $ R.zipWith (*) (slice m (Z:.i:.All)) $ slice v (sh':.All)
    in if mcols == vrows then fromFunction (sh :. mrows) f
       else error "mulMatVec: mcols != vdim"
{-# INLINABLE mulMat #-}

-- | multiplication by a diagonal matrix along innermost dim
mulDiag :: (Source r1 r, Source r2 r, Ring r)
           => Array r1 DIM1 r -> Array r2 DIM2 r -> Array D DIM2 r
mulDiag !diag !arr = fromFunction (extent arr) f
  where f idx@(_ :. i) = (arr ! idx) * (diag ! (Z:.i))
{-# INLINABLE mulDiag #-}

-- misc Tensor functions

-- | Embeds a scalar into a powerful-basis representation of a Repa array,
-- tagged by the cyclotomic index
scalarPow' :: forall m r . (Fact m, Additive r, Unbox r) => r -> Arr m r
scalarPow' = coerce . go (proxy totientFact (Proxy::Proxy m))
  where go n !r = let fct (Z:.0) = r
                      fct _ = LP.zero
                  in force $ fromFunction (Z:.n) fct
{-# INLINABLE scalarPow' #-}

-- | Forces a delayed array to a manifest array.
force :: (Shape sh, Unbox r) => Array D sh r -> Array U sh r
force = computeS
--force = runIdentity . computeP
{-# INLINABLE force #-}

-- copied implementations of functions we need that normally require
-- Num

-- | Sum the inner-most dimension of an array sequentially
sumS :: (Source r a, Elt a, Unbox a, Additive a, Shape sh)
  => Array r (sh :. Int) a
  -> Array U sh a
sumS = foldS (+) LP.zero
{-# INLINABLE sumS #-}

-- | Sum all array indices to a scalar sequentially
sumAllS :: (Shape sh, Source r a, Elt a, Unbox a, Additive a)
  => Array r sh a
  -> a
sumAllS = foldAllS (+) LP.zero
{-# INLINABLE sumAllS #-}
