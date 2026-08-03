import Mathlib
import PCRLean.Experimental.BiorthogonalRegularCentre

/-!
# Experimental regular centre from an invertible evaluation minor

A finite Fitting chart is represented by packet rows, test vectors, and an
explicit inverse for their square evaluation matrix.  The inverse matrix
constructs transverse vectors by finite linear combination.  These vectors are
biorthogonal to the packet, so the packet evaluation is split surjective and
defines the intrinsic actual regular centre of the preceding module.

Geometrically, the inverse certificate is produced after localizing where a
maximal minor is a unit.  This file does not prove that such charts cover every
proper Frobenius/Fitting core, nor that their centre ideals glue or transform
hereditarily.
-/

namespace PCRLean
namespace Experimental
namespace InvertibleMinorRegularCentre

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

abbrev Dual := Module.Dual K V

/-- A packet evaluation matrix together with an explicit right inverse. -/
structure MinorCertificate where
  packet : ι → Dual (K := K) (V := V)
  testVector : ι → V
  inverseCoeff : ι → ι → K
  inverse_identity : ∀ i j : ι,
    ∑ k : ι, inverseCoeff k j * packet i (testVector k) =
      if i = j then 1 else 0

namespace MinorCertificate

variable (C : MinorCertificate (K := K) (V := V) (ι := ι))

/-- Transverse vectors obtained by applying the inverse evaluation matrix to
the chosen test vectors. -/
def transverse (j : ι) : V :=
  ∑ k : ι, C.inverseCoeff k j • C.testVector k

/-- The inverse-minor construction is biorthogonal. -/
theorem packet_transverse (i j : ι) :
    C.packet i (C.transverse j) = if i = j then 1 else 0 := by
  rw [transverse]
  simp only [map_sum, map_smul]
  simpa [mul_comm] using C.inverse_identity i j

/-- Convert an invertible evaluation minor into the standard biorthogonal
packet certificate. -/
def toBiorthogonalFrame :
    BiorthogonalSplitFrame.Frame (K := K) (V := V) (ι := ι) where
  packet := C.packet
  transverse := C.transverse
  biorthogonal := C.packet_transverse

/-- The evaluation map associated to the minor is surjective. -/
theorem eval_surjective :
    Function.Surjective C.toBiorthogonalFrame.eval :=
  BiorthogonalRegularCentre.eval_surjective C.toBiorthogonalFrame

/-- The intrinsic actual centre cut out by the invertible-minor chamber. -/
def centreIdeal : Ideal (SymmetricAlgebra K V) :=
  BiorthogonalRegularCentre.centreIdeal C.toBiorthogonalFrame

/-- Exact symmetric-algebra quotient in the invertible-minor chamber. -/
noncomputable def quotientEquiv :
    (SymmetricAlgebra K V ⧸ C.centreIdeal) ≃+*
      SymmetricAlgebra K (ι → K) :=
  BiorthogonalRegularCentre.quotientEquiv C.toBiorthogonalFrame

/-- The invertible-minor centre is proper. -/
theorem centreIdeal_ne_top : C.centreIdeal ≠ ⊤ :=
  BiorthogonalRegularCentre.centreIdeal_ne_top C.toBiorthogonalFrame

/-- Assemble a proper finite-type regular centre from the invertible-minor
certificate. -/
noncomputable def certificate
    [IsNoetherianRing (SymmetricAlgebra K V)]
    [IsRegularRing (SymmetricAlgebra K (ι → K))] :
    SurjectiveFreeRegularCentre.Certificate C.toBiorthogonalFrame.eval :=
  BiorthogonalRegularCentre.certificate C.toBiorthogonalFrame

end MinorCertificate

end

end InvertibleMinorRegularCentre
end Experimental
end PCRLean
