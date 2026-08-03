import Mathlib
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import PCRLean.Experimental.SpanningMinorRegularCentre
import PCRLean.Experimental.RangeRestrictedRegularCentre

/-!
# Experimental range equivalence from a spanning minor

A spanning invertible minor does more than identify the common kernel.  The
range of the full evaluation map is canonically equivalent to the finite
coefficient space of the selected rows.

The forward map restricts a full coefficient vector to the selected rows.  The
inverse map evaluates the full packet on the explicit transverse section.  The
biorthogonal identity proves one inverse law; equality of full and selected
kernels proves the other.

Thus the full packet range has an explicit finite basis indexed by the selected
minor.  This converts the spanning-minor certificate directly into the finite
free image hypothesis of `RangeRestrictedRegularCentre`.
-/

namespace PCRLean
namespace Experimental
namespace SpanningMinorRangeEquiv

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R] [Nontrivial R] [IsRegularRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {Row : Type w}
variable {Pivot : Type x} [Fintype Pivot] [DecidableEq Pivot]

open SpanningMinorRegularCentre

variable (C : SpanningMinorRegularCentre.CertificateData
  (R := R) (V := V) (Row := Row) (Pivot := Pivot))

/-- Restrict a full-packet range vector to its selected coefficients. -/
def rangeToSelected :
    LinearMap.range (fullEval C.packet) →ₗ[R] (Pivot → R) where
  toFun y i := y.1 (C.selected i)
  map_add' := by
    intro y z
    funext i
    rfl
  map_smul' := by
    intro a y
    funext i
    rfl

/-- Reconstruct a full-packet range vector by evaluating the full packet on the
selected transverse section. -/
def selectedToRange :
    (Pivot → R) →ₗ[R] LinearMap.range (fullEval C.packet) where
  toFun a :=
    ⟨fullEval C.packet (C.selectedFrame.section a),
      ⟨C.selectedFrame.section a, rfl⟩⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    simp
  map_smul' := by
    intro a b
    apply Subtype.ext
    simp

/-- On a vector coming from the full evaluation map, restriction to selected
coordinates is exactly selected evaluation. -/
@[simp] theorem rangeToSelected_mk (x : V) :
    C.rangeToSelected
        ⟨fullEval C.packet x, ⟨x, rfl⟩⟩ =
      C.selectedEval x := by
  funext i
  rfl

/-- Reconstruction followed by selected restriction is the identity. -/
@[simp] theorem rangeToSelected_selectedToRange (a : Pivot → R) :
    C.rangeToSelected (C.selectedToRange a) = a := by
  funext i
  change C.selectedFrame.eval (C.selectedFrame.section a) i = a i
  exact congrFun (C.selectedFrame.eval_section a) i

/-- Selected restriction followed by reconstruction is the identity on the
full packet range. -/
@[simp] theorem selectedToRange_rangeToSelected
    (y : LinearMap.range (fullEval C.packet)) :
    C.selectedToRange (C.rangeToSelected y) = y := by
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨x, hx⟩
  subst y
  rw [C.rangeToSelected_mk]
  apply Subtype.ext
  change
    fullEval C.packet (C.selectedFrame.section (C.selectedEval x)) =
      fullEval C.packet x
  let z : V := C.selectedFrame.section (C.selectedEval x) - x
  have hselectedZero : C.selectedEval z = 0 := by
    dsimp [z]
    rw [map_sub, C.selectedFrame.eval_section]
    simp
  have hselectedKer : z ∈ LinearMap.ker C.selectedEval :=
    LinearMap.mem_ker.mpr hselectedZero
  have hfullKer : z ∈ LinearMap.ker (fullEval C.packet) := by
    rw [C.ker_fullEval_eq_selectedEval]
    exact hselectedKer
  have hfullZero : fullEval C.packet z = 0 :=
    LinearMap.mem_ker.mp hfullKer
  have hdiff :
      fullEval C.packet (C.selectedFrame.section (C.selectedEval x)) -
          fullEval C.packet x = 0 := by
    simpa [z, map_sub] using hfullZero
  exact sub_eq_zero.mp hdiff

/-- Explicit linear equivalence between the image of the full packet and the
selected coefficient space. -/
noncomputable def rangeEquivSelected :
    LinearMap.range (fullEval C.packet) ≃ₗ[R] (Pivot → R) where
  toLinearMap := C.rangeToSelected
  invFun := C.selectedToRange
  left_inv := C.selectedToRange_rangeToSelected
  right_inv := C.rangeToSelected_selectedToRange

/-- Explicit finite basis of the full packet range. -/
noncomputable def rangeBasis :
    Module.Basis Pivot R (LinearMap.range (fullEval C.packet)) :=
  (Pi.basisFun R Pivot).map C.rangeEquivSelected.symm

/-- The full packet range is free. -/
theorem range_free :
    Module.Free R (LinearMap.range (fullEval C.packet)) :=
  Module.Free.of_basis C.rangeBasis

/-- The full packet range is finite. -/
theorem range_finite :
    Module.Finite R (LinearMap.range (fullEval C.packet)) :=
  Module.Finite.of_basis C.rangeBasis

/-- The spanning-minor certificate therefore supplies the canonical
range-restricted actual regular centre. -/
noncomputable def rangeRegularCertificate
    [Module.Free R V] [Module.Finite R V] :
    RangeRestrictedRegularCentre.Certificate (fullEval C.packet) := by
  letI : Module.Free R (LinearMap.range (fullEval C.packet)) :=
    C.range_free
  letI : Module.Finite R (LinearMap.range (fullEval C.packet)) :=
    C.range_finite
  exact RangeRestrictedRegularCentre.finiteFreeCertificate
    (fullEval C.packet)

end

end SpanningMinorRangeEquiv
end Experimental
end PCRLean
