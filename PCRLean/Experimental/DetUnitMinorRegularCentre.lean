import Mathlib
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PCRLean.Experimental.InvertibleMinorRegularCentre

/-!
# Experimental regular centre from a determinant-unit minor

On a Fitting chart, a square packet-evaluation minor is invertible precisely
when its determinant is a unit. Mathlib's nonsingular matrix inverse then
supplies the explicit inverse coefficients required by
`InvertibleMinorRegularCentre.MinorCertificate`.

Consequently a determinant-unit Jacobian minor on a regular affine chart
constructs transverse vectors, a split packet evaluation, and an intrinsic
actual proper regular centre. For a finite free source over a Noetherian regular
base, no additional local algebraic input remains.

This is still a local chart theorem. It does not prove that determinant-unit
minor charts cover every proper Frobenius/Fitting core, nor localization descent
of the resulting centre ideal or hereditary transform compatibility.
-/

namespace PCRLean
namespace Experimental
namespace DetUnitMinorRegularCentre

noncomputable section

universe u v w

variable {K : Type u} [CommRing K] [Nontrivial K] [IsRegularRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

abbrev Dual := Module.Dual K V

/-- Packet rows and test vectors whose square evaluation minor has unit
determinant. -/
structure UnitMinorCertificate where
  packet : ι → Dual (K := K) (V := V)
  testVector : ι → V
  det_isUnit : IsUnit
    (Matrix.det (Matrix.of fun i j : ι => packet i (testVector j)))

namespace UnitMinorCertificate

variable (C : UnitMinorCertificate (K := K) (V := V) (ι := ι))

/-- The square evaluation matrix of the selected minor. -/
def evaluationMatrix : Matrix ι ι K :=
  Matrix.of fun i j => C.packet i (C.testVector j)

/-- Inverse coefficients supplied canonically by the nonsingular matrix
inverse. -/
def inverseCoeff (k j : ι) : K :=
  (C.evaluationMatrix⁻¹) k j

/-- The determinant-unit hypothesis gives exactly the coefficient identity
required by the explicit inverse-minor certificate. -/
theorem inverse_identity (i j : ι) :
    ∑ k : ι, C.inverseCoeff k j * C.packet i (C.testVector k) =
      if i = j then 1 else 0 := by
  have hmul : C.evaluationMatrix * C.evaluationMatrix⁻¹ = 1 :=
    Matrix.mul_nonsing_inv C.evaluationMatrix C.det_isUnit
  have hij := congrArg (fun M : Matrix ι ι K => M i j) hmul
  simpa [evaluationMatrix, inverseCoeff, Matrix.mul_apply, mul_comm] using hij

/-- Compile the determinant-unit chart into the explicit inverse-minor
interface. -/
def toMinorCertificate :
    InvertibleMinorRegularCentre.MinorCertificate
      (K := K) (V := V) (ι := ι) where
  packet := C.packet
  testVector := C.testVector
  inverseCoeff := C.inverseCoeff
  inverse_identity := C.inverse_identity

/-- The determinant-unit minor determines the intrinsic actual centre ideal. -/
def centreIdeal : Ideal (SymmetricAlgebra K V) :=
  C.toMinorCertificate.centreIdeal

/-- Exact quotient theorem in the determinant-unit chamber. -/
noncomputable def quotientEquiv :
    (SymmetricAlgebra K V ⧸ C.centreIdeal) ≃+*
      SymmetricAlgebra K (ι → K) :=
  C.toMinorCertificate.quotientEquiv

/-- Properness of the determinant-unit centre. -/
theorem centreIdeal_ne_top : C.centreIdeal ≠ ⊤ :=
  C.toMinorCertificate.centreIdeal_ne_top

/-- Assemble the regular-centre certificate when the ambient symmetric algebra
is Noetherian. -/
noncomputable def certificate
    [IsNoetherianRing (SymmetricAlgebra K V)] :
    SurjectiveFreeRegularCentre.Certificate
      C.toMinorCertificate.toBiorthogonalFrame.eval :=
  C.toMinorCertificate.certificate

/-- For a finite free source over a Noetherian regular base, a unit determinant
minor is the only local algebraic input. -/
noncomputable def finiteFreeCertificate
    [IsNoetherianRing K]
    [Module.Free K V] [Module.Finite K V] :
    SurjectiveFreeRegularCentre.Certificate
      C.toMinorCertificate.toBiorthogonalFrame.eval :=
  C.toMinorCertificate.finiteFreeCertificate

end UnitMinorCertificate

end

end DetUnitMinorRegularCentre
end Experimental
end PCRLean
