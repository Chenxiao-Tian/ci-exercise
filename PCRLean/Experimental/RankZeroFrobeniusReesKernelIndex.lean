import PCRLean.Experimental.PDerivFrobeniusDescent
import PCRLean.Experimental.FrobeniusPrimitiveDecomposition
import PCRLean.Experimental.DerivativeZeroFinitePresentation
import PCRLean.Experimental.InitialFormFrobeniusCleaning
import PCRLean.Experimental.InitialFormCleaningTermination
import PCRLean.Experimental.ReesFrobeniusIntegralCompression
import PCRLean.Experimental.FiniteReesFrobeniusCompression
import PCRLean.Experimental.FiniteHasseIntegralCompression
import PCRLean.Experimental.IntegralEquivalentReesPresentations
import PCRLean.Experimental.PolynomialHasseFrobenius
import PCRLean.Experimental.UnivariateHasseIntegralCompression
import PCRLean.Experimental.RankZeroFrobeniusReesExit
import PCRLean.Experimental.ImperfectCoefficientObstruction

/-!
# Integrated rank-zero Frobenius--Rees kernel index

This isolated index records the strongest current perfect-field rank-zero
candidate kernel.

Polynomial and initial-form layer:

* all first partial derivatives zero forces every supported exponent to be
  divisible by the characteristic;
* over a perfect field the polynomial has an explicit `p`-th root;
* a nonconstant root strictly lowers total degree;
* every polynomial has a finite Frobenius-primitive decomposition;
* finite derivative-zero presentations admit a canonical root packet, marked
  permissibility, and a strict total-degree-mass descent;
* a rank-zero lowest homogeneous initial layer is removed exactly by cleaning;
* nonzero cleaning strictly lowers monomial-support cardinality, so an infinite
  cleaning chain is impossible.

Rees and Hasse layer:

* a lower-weight Frobenius root is integral over the algebra containing its
  weighted `p`-th power;
* adjoining one or finitely many roots is a finite integral extension;
* the source and root presentations have the same ambient integral elements;
* a finite operator packet satisfying the Hasse--Frobenius power identity gives
  the same finite integral compression;
* for ordinary polynomial Hasse derivatives the required identity
  `D^[p*k](f^p) = (D^[k]f)^p` is proved from Taylor coefficients;
* finite low-order root Hasse packets therefore give concrete integrally
  equivalent presentations.

Boundary:

* over an imperfect field, `a X^p` can have zero derivative and no polynomial
  `p`-th root when `a` is not in the Frobenius image;
* none of these normalization results by itself constructs a legal blowup
  centre;
* the missing geometric bridge is invariance of singular loci, legal centres,
  controlled transforms, owners, boundary data and history under integral
  equivalence of differential Rees presentations.

The file does not prove arbitrary-dimensional positive-characteristic
resolution and is not imported by the certified index.
-/

namespace PCRLean.Experimental.RankZeroFrobeniusReesKernelIndex

#print axioms PCRLean.Experimental.PDerivFrobeniusDescent.visible_or_strict_root
#print axioms PCRLean.Experimental.FrobeniusPrimitiveDecomposition.exists_frobeniusPrimitive_decomposition
#print axioms PCRLean.Experimental.DerivativeZeroFinitePresentation.markedPresentation_permissible
#print axioms PCRLean.Experimental.DerivativeZeroFinitePresentation.no_infinite_rootPacket_chain
#print axioms PCRLean.Experimental.InitialFormFrobeniusCleaning.InitialDecomposition.cleaned_higher
#print axioms PCRLean.Experimental.InitialFormCleaningTermination.no_infinite_cleaning_chain
#print axioms PCRLean.Experimental.ReesFrobeniusIntegralCompression.rootAdjoin_moduleFinite
#print axioms PCRLean.Experimental.ReesFrobeniusIntegralCompression.isIntegralPolynomial_rootAdjoin_iff
#print axioms PCRLean.Experimental.FiniteReesFrobeniusCompression.Presentation.rootAdjoin_moduleFinite
#print axioms PCRLean.Experimental.FiniteHasseIntegralCompression.Packet.rootOperatorAdjoin_moduleFinite
#print axioms PCRLean.Experimental.IntegralEquivalentReesPresentations.finiteHasseSource_integralEquivalent
#print axioms PCRLean.Experimental.PolynomialHasseFrobenius.hasseDeriv_pow_prime
#print axioms PCRLean.Experimental.PolynomialHasseFrobenius.hasseDeriv_pow_primePower
#print axioms PCRLean.Experimental.UnivariateHasseIntegralCompression.source_root_integralEquivalent
#print axioms PCRLean.Experimental.RankZeroFrobeniusReesExit.InitialDecomposition.integral_cleaning_exit
#print axioms PCRLean.Experimental.ImperfectCoefficientObstruction.derivative_zero_but_no_root

end PCRLean.Experimental.RankZeroFrobeniusReesKernelIndex
