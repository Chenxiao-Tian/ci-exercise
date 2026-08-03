import Mathlib
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PCRLean.Experimental.InvertibleMinorRegularCentre

/-!
# Experimental regular centre from a unit determinant minor

A square evaluation minor is obtained by evaluating a finite packet of conormal
rows on finitely many test vectors. If its determinant is a unit, the
nonsingular matrix inverse supplies the explicit inverse-coefficient certificate
required by `InvertibleMinorRegularCentre`.

Consequently, over a nontrivial regular base ring and for a finite free source
module, a unit determinant minor produces an intrinsic actual proper finite-type
regular centre. This is the direct algebraic form of a Fitting principal chart.

The theorem begins after the determinant has become a unit. Showing that the
corresponding principal opens cover the required Frobenius/Fitting core, and
proving localization descent and hereditary blowup transport, remain separate
obligations.
-/

namespace PCRLean
namespace Experimental
namespace DeterminantMinorRegularCentre

noncomputable section

universe u v w

variable {K : Type u} [CommRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

abbrev Dual := Module.Dual K V

/-- Square evaluation matrix of packet rows on test vectors. -/
def evaluationMatrix
    (packet : ι → Dual (K := K) (V := V))
    (testVector : ι → V) : Matrix ι ι K :=
  fun i j => packet i (testVector j)

/-- A unit determinant supplies the explicit inverse identity used by the
minor-certificate layer. -/
theorem inverse_identity
    (packet : ι → Dual (K := K) (V := V))
    (testVector : ι → V)
    (hdet : IsUnit (evaluationMatrix packet testVector).det)
    (i j : ι) :
    ∑ k : ι,
        (evaluationMatrix packet testVector)⁻¹ k j *
          packet i (testVector k) =
      if i = j then 1 else 0 := by
  have hmul := congrArg
    (fun M : Matrix ι ι K => M i j)
    (Matrix.mul_nonsing_inv (evaluationMatrix packet testVector) hdet)
  simpa [Matrix.mul_apply, evaluationMatrix, mul_comm] using hmul

/-- Convert a unit determinant minor into the explicit inverse-minor
certificate. -/
noncomputable def toMinorCertificate
    [Nontrivial K] [IsRegularRing K]
    (packet : ι → Dual (K := K) (V := V))
    (testVector : ι → V)
    (hdet : IsUnit (evaluationMatrix packet testVector).det) :
    InvertibleMinorRegularCentre.MinorCertificate
      (K := K) (V := V) (ι := ι) where
  packet := packet
  testVector := testVector
  inverseCoeff := fun k j =>
    (evaluationMatrix packet testVector)⁻¹ k j
  inverse_identity := inverse_identity packet testVector hdet

/-- A unit determinant evaluation minor gives a surjective packet evaluation
map. -/
theorem eval_surjective
    [Nontrivial K] [IsRegularRing K]
    (packet : ι → Dual (K := K) (V := V))
    (testVector : ι → V)
    (hdet : IsUnit (evaluationMatrix packet testVector).det) :
    Function.Surjective
      (toMinorCertificate packet testVector hdet).toBiorthogonalFrame.eval :=
  (toMinorCertificate packet testVector hdet).eval_surjective

/-- Over a regular base with finite free source, a unit determinant minor is a
complete local actual regular-centre certificate. -/
noncomputable def finiteFreeCertificate
    [Nontrivial K] [IsRegularRing K]
    [Module.Free K V] [Module.Finite K V]
    (packet : ι → Dual (K := K) (V := V))
    (testVector : ι → V)
    (hdet : IsUnit (evaluationMatrix packet testVector).det) :
    SurjectiveFreeRegularCentre.Certificate
      (toMinorCertificate packet testVector hdet).toBiorthogonalFrame.eval :=
  (toMinorCertificate packet testVector hdet).finiteFreeCertificate

end

end DeterminantMinorRegularCentre
end Experimental
end PCRLean
