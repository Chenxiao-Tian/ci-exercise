import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PCRLean.Experimental.SurjectiveFiniteDimensionalRegularCentre

/-!
# Experimental intrinsic regular centre from an arbitrary finite linear packet

Every linear map factors canonically as a surjection onto its range followed by
the range inclusion.  The range-restricted map has exactly the same kernel as
the original map.  Consequently every linear map between finite-dimensional
vector spaces over a field determines an intrinsic degree-one ideal whose
symmetric-algebra quotient is regular.  No constant-rank, surjectivity, basis,
or splitting hypothesis remains in the theorem interface.

This is an algebraic effectivity theorem for one finite packet.  It does not
show that the resulting centre is permissible for a marked singularity, that
packet formation commutes with nonlinear blowup transforms, or that local
packets glue globally.
-/

namespace PCRLean
namespace Experimental
namespace ArbitraryFiniteLinearPacketRegularCentre

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

open IntrinsicKernelIdealFunctoriality

/-- Canonical surjection from the source onto the range of a linear packet. -/
def rangeProjection (project : V →ₗ[K] W) :
    V →ₗ[K] LinearMap.range project :=
  project.rangeRestrict

/-- The canonical range projection is surjective. -/
theorem rangeProjection_surjective (project : V →ₗ[K] W) :
    Function.Surjective (rangeProjection project) := by
  rintro ⟨y, hy⟩
  rcases hy with ⟨x, rfl⟩
  exact ⟨x, rfl⟩

/-- Restricting the codomain to the range does not change the kernel. -/
theorem rangeProjection_ker_eq (project : V →ₗ[K] W) :
    (rangeProjection project).ker = project.ker := by
  ext x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    have hsub := LinearMap.mem_ker.mp hx
    have hval := congrArg Subtype.val hsub
    simpa [rangeProjection] using hval
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    simpa [rangeProjection] using LinearMap.mem_ker.mp hx

/-- Intrinsic centre ideal of the arbitrary packet. -/
def centreIdeal (project : V →ₗ[K] W) :
    Ideal (SymmetricAlgebra K V) :=
  kernelIdealOf project

/-- The original packet ideal agrees with the intrinsic ideal of the canonical
surjection onto its range. -/
theorem centreIdeal_eq_rangeCentreIdeal (project : V →ₗ[K] W) :
    centreIdeal project =
      SurjectiveFiniteDimensionalRegularCentre.centreIdeal
        (rangeProjection project) := by
  unfold centreIdeal SurjectiveFiniteDimensionalRegularCentre.centreIdeal
  exact kernelIdealOf_eq_of_ker_eq project (rangeProjection project)
    (rangeProjection_ker_eq project).symm

section FiniteDimensional

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- Exact quotient theorem for an arbitrary finite-dimensional packet. -/
noncomputable def quotientEquiv (project : V →ₗ[K] W) :
    (SymmetricAlgebra K V ⧸ centreIdeal project) ≃+*
      SymmetricAlgebra K (LinearMap.range project) :=
  (Ideal.quotEquivOfEq (centreIdeal_eq_rangeCentreIdeal project)).trans
    (SurjectiveFiniteDimensionalRegularCentre.quotientEquiv
      (rangeProjection project) (rangeProjection_surjective project))

/-- Properness of the arbitrary packet centre. -/
theorem centreIdeal_ne_top (project : V →ₗ[K] W) :
    centreIdeal project ≠ ⊤ := by
  rw [centreIdeal_eq_rangeCentreIdeal project]
  exact SurjectiveFiniteDimensionalRegularCentre.centreIdeal_ne_top
    (rangeProjection project) (rangeProjection_surjective project)

/-- Finite generation of the arbitrary packet centre. -/
theorem centreIdeal_fg (project : V →ₗ[K] W) :
    (centreIdeal project).FG := by
  rw [centreIdeal_eq_rangeCentreIdeal project]
  exact SurjectiveFiniteDimensionalRegularCentre.centreIdeal_fg
    (rangeProjection project) (rangeProjection_surjective project)

/-- Regularity of the arbitrary packet quotient. -/
theorem quotient_isRegularRing (project : V →ₗ[K] W) :
    IsRegularRing (SymmetricAlgebra K V ⧸ centreIdeal project) := by
  rw [centreIdeal_eq_rangeCentreIdeal project]
  exact SurjectiveFiniteDimensionalRegularCentre.quotient_isRegularRing
    (rangeProjection project) (rangeProjection_surjective project)

/-- Choice-free actual regular-centre certificate for an arbitrary finite
linear packet. -/
structure Certificate (project : V →ₗ[K] W) where
  ideal : Ideal (SymmetricAlgebra K V)
  ideal_eq : ideal = centreIdeal project
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient :
    (SymmetricAlgebra K V ⧸ ideal) ≃+*
      SymmetricAlgebra K (LinearMap.range project)
  quotientRegular : IsRegularRing (SymmetricAlgebra K V ⧸ ideal)

/-- Assemble the choice-free certificate. -/
noncomputable def certificate (project : V →ₗ[K] W) :
    Certificate project where
  ideal := centreIdeal project
  ideal_eq := rfl
  proper := centreIdeal_ne_top project
  finiteType := centreIdeal_fg project
  quotient := quotientEquiv project
  quotientRegular := quotient_isRegularRing project

end FiniteDimensional

end

end ArbitraryFiniteLinearPacketRegularCentre
end Experimental
end PCRLean
