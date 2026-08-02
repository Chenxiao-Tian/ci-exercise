import Mathlib
import PCRLean.MatrixStableSubmodule

/-!
# Finite-free endomorphism descent

The matrix classification is basis independent. A submodule of any finite
free module that is stable under every endomorphism becomes, in every chosen
basis, the coordinatewise extension of one ideal of the base ring. This is the
basis-transport form needed for finite-level Frobenius descent.

For a smooth characteristic-`p` algebra, relative Frobenius is finite locally
free. Once the level-`e` differential operators are identified with the full
endomorphism algebra over the Frobenius twist, this theorem classifies every
operator-stable ideal locally as an extended ideal from that twist.
-/

namespace PCRLean
namespace FiniteFreeEndomorphismDescent

noncomputable section

universe u v w

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [Fintype ι] [DecidableEq ι]

abbrev Coordinates := ι → R

/-- Invariance of a submodule under the full endomorphism algebra. -/
def FullyInvariant (N : Submodule R M) : Prop :=
  ∀ T : Module.End R M, ∀ x, x ∈ N → T x ∈ N

/-- Conjugate an endomorphism through a linear equivalence. -/
def conjugateEnd (e : M ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (T : Module.End R (Coordinates (R := R) (ι := ι))) : Module.End R M :=
  e.symm.toLinearMap.comp (T.comp e.toLinearMap)

@[simp] theorem apply_conjugateEnd
    (e : M ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (T : Module.End R (Coordinates (R := R) (ι := ι))) (x : M) :
    e (conjugateEnd e T x) = T (e x) := by
  simp [conjugateEnd]

/-- Full invariance is transported to coordinates by any basis equivalence. -/
theorem map_fullyInvariant
    (e : M ≃ₗ[R] Coordinates (R := R) (ι := ι))
    {N : Submodule R M} (hN : FullyInvariant N) :
    MatrixStableSubmodule.FullyInvariant (N.map e.toLinearMap) := by
  intro T y hy
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨conjugateEnd e T x, hN (conjugateEnd e T) x hx, ?_⟩
  exact apply_conjugateEnd e T x

/-- In coordinates, a fully invariant submodule is the extension of one ideal
of the base ring. -/
theorem exists_coordinate_ideal
    (e : M ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (N : Submodule R M) (hN : FullyInvariant N) :
    ∃ J : Ideal R,
      N.map e.toLinearMap = MatrixStableSubmodule.fromIdeal (ι := ι) J := by
  let Ncoord : Submodule R (Coordinates (R := R) (ι := ι)) :=
    N.map e.toLinearMap
  have hcoord : MatrixStableSubmodule.FullyInvariant Ncoord :=
    map_fullyInvariant e hN
  exact ⟨MatrixStableSubmodule.coordinateIdeal Ncoord,
    MatrixStableSubmodule.eq_fromIdeal Ncoord hcoord⟩

/-- Exact coefficientwise membership formula in a chosen finite-free frame. -/
theorem mem_iff_coefficients_mem
    (e : M ≃ₗ[R] Coordinates (R := R) (ι := ι))
    {N : Submodule R M} (hN : FullyInvariant N) (x : M) :
    x ∈ N ↔ ∀ i,
      e x i ∈ MatrixStableSubmodule.coordinateIdeal (N.map e.toLinearMap) := by
  constructor
  · intro hx
    have hmap : e x ∈ N.map e.toLinearMap := ⟨x, hx, rfl⟩
    exact (MatrixStableSubmodule.mem_iff_forall_coordinate_mem
      (map_fullyInvariant e hN) (e x)).mp hmap
  · intro hx
    have hmap : e x ∈ N.map e.toLinearMap :=
      (MatrixStableSubmodule.mem_iff_forall_coordinate_mem
        (map_fullyInvariant e hN) (e x)).mpr hx
    rcases hmap with ⟨y, hy, hey⟩
    have : y = x := e.injective hey
    simpa [this] using hy

/-- Mapping back the coordinate classification recovers the original
submodule. -/
theorem eq_comap_fromIdeal
    (e : M ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (N : Submodule R M) (hN : FullyInvariant N) :
    N = (MatrixStableSubmodule.fromIdeal (ι := ι)
      (MatrixStableSubmodule.coordinateIdeal (N.map e.toLinearMap))).comap
        e.toLinearMap := by
  ext x
  simp only [Submodule.mem_comap]
  exact mem_iff_coefficients_mem e hN x

end

end FiniteFreeEndomorphismDescent
end PCRLean
