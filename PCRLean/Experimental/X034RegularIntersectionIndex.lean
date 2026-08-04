import PCRLean.Experimental.TorExcessIsZeroExcess
import PCRLean.Experimental.SplitExcessKernel
import PCRLean.Experimental.ProjectivityDiscriminantPrime

/-!
# MLEL-X034 / RIC-PD-WOS integrated experimental index

This round corrects the X033 geometric discriminator.

```text
Tor independence = zero excess = transverse subchamber,
not the universal clean-intersection condition.
```

The corrected candidate architecture is:

```text
finite minimizer intersection arrangement
-> every nonempty scheme-theoretic intersection is a regular immersion
-> conormal maps are surjective between finite projective modules
-> excess kernels are finite projective, possibly nonzero
-> clean arrangement
-> deepest-first wonderful ordinary-centre serialization

first nonregular/non-quasi-regular intersection
-> projectivity/normal-cone/Fitting defect carrier
-> Schur-Fitting or kernel-regularization recursion.
```

The source proves only the local algebraic leaves:

* nested non-idempotent pairs necessarily have Tor excess;
* a split conormal surjection has a projective kernel;
* product-ideal support over prime ideals has the exact Boolean law required
  by the projectivity discriminant.

It does not prove the scheme-level regular-intersection theorem, the wonderful
serialization theorem, strict descent of the defect branch, joint owner
legality, hereditary no-reset, termination, globalization, or general
positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X034RegularIntersectionIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X034RegularIntersectionIndex
end Experimental
end PCRLean
