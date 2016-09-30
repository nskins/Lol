{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}

module Crypto.Lol.FactoredT
(module Crypto.Lol.FactoredT,
 module Crypto.Lol.Factored) where

import qualified Crypto.Lol.Factored as F
import Crypto.Lol.Factored hiding (transDivides,
                                   gcdDivides, lcmDivides, lcm2Divides,
                                   pSplitTheorems, pFreeDivides, ppPPow,
                                   ppsFact, valuePrime, valueFact,
                                   totientFact, radicalFact, oddRadicalFact,
                                   valueHatFact, primePPow, exponentPPow,
                                   valuePPow, totientPPow, radicalPPow,
                                   oddRadicalPPow, valueHatPPow)
import Data.Constraint
import Data.Functor.Trans.Tagged
import Data.Proxy

-- coercions: using proxy arguments here due to compiler bugs in usage

-- | Entails constraint for transitivity of division, i.e.
-- if \( k \mid l \) and \( l \mid m \), then \( k \mid m \).
transDivides' :: forall k l m . Proxy k -> Proxy l -> Proxy m ->
                 ((k `Divides` l, l `Divides` m) :- (k `Divides` m))
transDivides' _ _ _ = F.transDivides @k @l @m

-- | Entailment for divisibility by GCD:
-- if \( g=\gcd(m_1,m_2) \) then \( g \mid m_1 \) and \( g \mid m_2 \).
gcdDivides' :: forall m1 m2 g . Proxy m1 -> Proxy m2 ->
               ((Fact m1, Fact m2, g ~ FGCD m1 m2) :-
                (g `Divides` m1, g `Divides` m2))
gcdDivides' _ _ = F.gcdDivides @m1 @m2

-- | Entailment for LCM divisibility:
-- if \( l=\lcm(m_1,m_2) \) then \( m_1 \mid l \) and \( m_2 \mid l \).
lcmDivides' :: forall m1 m2 l . Proxy m1 -> Proxy m2 ->
               ((Fact m1, Fact m2, l ~ FLCM m1 m2) :-
                (m1 `Divides` l, m2 `Divides` l))
lcmDivides' _ _ = F.lcmDivides @m1 @m2

-- | Entailment for LCM divisibility:
-- the LCM of two divisors of \( m \) also divides \( m \).
lcm2Divides' :: forall m1 m2 l m . Proxy m1 -> Proxy m2 -> Proxy m ->
                ((m1 `Divides` m, m2 `Divides` m, l ~ FLCM m1 m2) :-
                 (m1 `Divides` l, m2 `Divides` l, (FLCM m1 m2) `Divides` m))
lcm2Divides' _ _ _ = F.lcm2Divides @m1 @m2 @m

-- | Entailment for \( p \)-free division:
-- if \( f \) is \(m \) after removing all \( p \)-factors, then \( f \mid m \)
-- and \( \gcd(f,p)=1 \).
pSplitTheorems' :: forall p m f . Proxy p -> Proxy m ->
                   ((Prime p, Fact m, f ~ PFree p m) :-
                    (f `Divides` m, Coprime (PToF p) f))
pSplitTheorems' _ _ = F.pSplitTheorems @p @m

-- | Entailment for \( p \)-free division:
-- if \( m \mid m' \), then \( \text{p-free}(m) \mid \text{p-free}(m') \).
pFreeDivides' :: forall p m m' . Proxy p -> Proxy m -> Proxy m' ->
                 ((Prime p, m `Divides` m') :-
                  ((PFree p m) `Divides` (PFree p m')))
pFreeDivides' _ _ _ = F.pFreeDivides @p @m @m'

-- | Reflect a 'PrimePower' type to a 'PP' value.
ppPPow' :: forall pp . PPow pp => Tagged pp PP
ppPPow' = tag $ F.ppPPow @pp

-- | Value-level prime-power factorization tagged by a 'Factored' type.
ppsFact' :: forall m . Fact m => Tagged m [PP]
ppsFact' = tag $ F.ppsFact @m

-- | The value of a 'PrimeBin' type.
valuePrime' :: forall p . Prime p => Tagged p Int
valuePrime' = tag $ F.valuePrime @p


valueFact', totientFact', radicalFact', oddRadicalFact', valueHatFact' ::
  forall m . Fact m => Tagged m Int
-- | The value of a 'Factored' type.
valueFact' = tag $ F.valueFact @m
-- | The totient of a 'Factored' type's value.
totientFact' = tag $ F.totientFact @m
-- | The "hat" of a 'Factored' type's value:
-- \( \hat{m} = \begin{cases} m & \mbox{if } m \text{ is odd} \\ m/2 & \text{otherwise} \end{cases} \).
valueHatFact' = tag $ F.valueHatFact @m
-- | The radical (product of prime divisors) of a 'Factored' type.
radicalFact' = tag $ F.radicalFact @m
-- | The odd radical (product of odd prime divisors) of a 'Factored' type.
oddRadicalFact' = tag $ F.oddRadicalFact @m

primePPow', exponentPPow', valuePPow', totientPPow', radicalPPow', oddRadicalPPow', valueHatPPow' ::
  forall pp . PPow pp => Tagged pp Int
-- | Reflect the prime component of a 'PrimePower' type.
primePPow' = tag $ F.primePPow @pp
-- | Reflect the exponent component of a 'PrimePower' type.
exponentPPow' = tag $ F.exponentPPow @pp
-- | The value of a 'PrimePower' type.
valuePPow' = tag $ F.valuePPow @pp
-- | The totient of a 'PrimePower' type's value.
totientPPow' = tag $ F.totientPPow @pp
-- | The "hat" of a 'PrimePower' type's value:
-- \( p^e \) if \( p \) is odd, \( 2^{e-1} \) otherwise.
valueHatPPow' = tag $ F.valueHatPPow @pp
-- | The radical of a 'PrimePower' type's value.
radicalPPow' = tag $ F.radicalPPow @pp
-- | The odd radical of a 'PrimePower' type's value.
oddRadicalPPow' = tag $ F.oddRadicalPPow @pp