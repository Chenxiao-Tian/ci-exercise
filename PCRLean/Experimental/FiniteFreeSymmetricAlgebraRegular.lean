import Mathlib
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Finite free symmetric algebras are finite type, Noetherian, and regular

A finite free module has a basis indexed by a finite type. Its symmetric
algebra is therefore algebra-equivalent to a polynomial ring in finitely many
variables. Hilbert's basis theorem gives Noetherianity over a Noetherian base,
and polynomial regularity gives regularity over a regular base.

No field hypothesis is needed. This file isolates the ring-theoretic automation
required by intrinsic conormal-centre certificates on regular affine charts and
their localizations.
-/

namespace PCRLean
namespace Experimental
namespace FiniteFreeSymmetricAlgebraRegular

noncomputable section

universe u v

variable {K : Type u} [CommRing K]
variable {M : Type v} [AddCommGroup M] [Module K M]
variable [Module.Free K M] [Module.Finite K M]

/-- A finite free symmetric algebra is of finite type over the ground ring. -/
theorem finiteType : Algebra.FiniteType K (SymmetricAlgebra K M) := by
  let b := Module.Free.chooseBasis K M
  letI : Fintype (Module.Free.ChooseBasisIndex K M) :=
    Module.Free.ChooseBasisIndex.fintype K M
  have hpoly : Algebra.FiniteType K
      (MvPolynomial (Module.Free.ChooseBasisIndex K M) K) := by
    infer_instance
  exact Algebra.FiniteType.equiv hpoly
    (SymmetricAlgebra.equivMvPolynomial b).symm

/-- Hilbert's basis theorem transferred through the polynomial model. -/
theorem isNoetherianRing [IsNoetherianRing K] :
    IsNoetherianRing (SymmetricAlgebra K M) := by
  letI : Algebra.FiniteType K (SymmetricAlgebra K M) := finiteType
  exact Algebra.FiniteType.isNoetherianRing K (SymmetricAlgebra K M)

/-- Polynomial regularity transferred through the basis equivalence. -/
theorem isRegularRing [IsRegularRing K] :
    IsRegularRing (SymmetricAlgebra K M) := by
  let b := Module.Free.chooseBasis K M
  letI : Fintype (Module.Free.ChooseBasisIndex K M) :=
    Module.Free.ChooseBasisIndex.fintype K M
  haveI : IsRegularRing
      (MvPolynomial (Module.Free.ChooseBasisIndex K M) K) := by
    infer_instance
  exact IsRegularRing.of_ringEquiv
    (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv

end

end FiniteFreeSymmetricAlgebraRegular
end Experimental
end PCRLean
