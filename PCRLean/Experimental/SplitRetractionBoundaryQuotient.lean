import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Boundary quotients for split ring retractions

Let `f : A →+* B` admit a ring section `s : B →+* A`.  For every ideal
`J ⊂ B`, the composite

`A --f--> B --> B/J`

has kernel exactly

`ker(f) ⊔ map(s, J)`.

Consequently

`A / (ker(f) + s(J)) ≃ B / J`.

For a polynomial graph centre, `f` is graph evaluation and `s` is the
coefficient inclusion.  The theorem then identifies every intersection of the
graph centre with a boundary stratum on the coefficient ring.  Regularity or
SNC of that stratum is therefore reduced to the corresponding quotient of the
coefficient ring.
-/

namespace PCRLean
namespace Experimental
namespace SplitRetractionBoundaryQuotient

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

/-- A split surjective ring map. -/
structure Retraction where
  project : A →+* B
  section : B →+* A
  project_section : project.comp section = RingHom.id B

namespace Retraction

variable (S : Retraction (A := A) (B := B))

/-- Pointwise form of the retraction identity. -/
@[simp] theorem project_section_apply (b : B) :
    S.project (S.section b) = b := by
  have h := congrArg (fun f : B →+* B => f b) S.project_section
  simpa [RingHom.comp_apply] using h

/-- The ideal obtained by combining the centre kernel and a boundary ideal from
the retract. -/
def liftedBoundaryIdeal (J : Ideal B) : Ideal A :=
  RingHom.ker S.project ⊔ J.map S.section

/-- Composite quotient map. -/
def boundaryMap (J : Ideal B) : A →+* B ⧸ J :=
  (Ideal.Quotient.mk J).comp S.project

/-- The composite quotient map is surjective. -/
theorem boundaryMap_surjective (J : Ideal B) :
    Function.Surjective (S.boundaryMap J) := by
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨S.section b, ?_⟩
  simp [boundaryMap]

/-- Exact kernel of the boundary quotient map. -/
theorem ker_boundaryMap_eq_liftedBoundaryIdeal (J : Ideal B) :
    RingHom.ker (S.boundaryMap J) = S.liftedBoundaryIdeal J := by
  apply le_antisymm
  · intro a ha
    have hquot : Ideal.Quotient.mk J (S.project a) = 0 :=
      RingHom.mem_ker.mp ha
    have hproj : S.project a ∈ J := by
      rwa [Ideal.Quotient.eq_zero_iff_mem] at hquot
    have hsection : S.section (S.project a) ∈ J.map S.section :=
      Ideal.mem_map_of_mem S.section hproj
    have hkernel : a - S.section (S.project a) ∈ RingHom.ker S.project := by
      apply RingHom.mem_ker.mpr
      simp
    have hleft : a - S.section (S.project a) ∈ S.liftedBoundaryIdeal J :=
      le_sup_left hkernel
    have hright : S.section (S.project a) ∈ S.liftedBoundaryIdeal J :=
      le_sup_right hsection
    have hadd := (S.liftedBoundaryIdeal J).add_mem hleft hright
    simpa using hadd
  · apply sup_le
    · intro a ha
      apply RingHom.mem_ker.mpr
      have hzero := RingHom.mem_ker.mp ha
      simp [boundaryMap, hzero]
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap]
      apply RingHom.mem_ker.mpr
      simp [boundaryMap, hb]

/-- Exact quotient by the centre kernel plus a lifted boundary ideal. -/
noncomputable def quotientEquiv (J : Ideal B) :
    (A ⧸ S.liftedBoundaryIdeal J) ≃+* (B ⧸ J) :=
  (Ideal.quotEquivOfEq
      (S.ker_boundaryMap_eq_liftedBoundaryIdeal J).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := S.boundaryMap J) (S.boundaryMap_surjective J))

/-- Equality of two boundary ideals can be checked after lifting them through a
split retraction. -/
theorem liftedBoundaryIdeal_injective :
    Function.Injective S.liftedBoundaryIdeal := by
  intro I J hIJ
  apply le_antisymm
  · intro b hb
    have hs : S.section b ∈ S.liftedBoundaryIdeal I :=
      le_sup_right (Ideal.mem_map_of_mem S.section hb)
    rw [hIJ] at hs
    have hmap := congrArg S.project
      (show S.section b = S.section b from rfl)
    have hquot :
        Ideal.Quotient.mk J b = 0 := by
      have hk : S.section b ∈ RingHom.ker (S.boundaryMap J) := by
        rwa [S.ker_boundaryMap_eq_liftedBoundaryIdeal J]
      have := RingHom.mem_ker.mp hk
      simpa [boundaryMap] using this
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hquot
  · intro b hb
    have hs : S.section b ∈ S.liftedBoundaryIdeal J :=
      le_sup_right (Ideal.mem_map_of_mem S.section hb)
    rw [← hIJ] at hs
    have hk : S.section b ∈ RingHom.ker (S.boundaryMap I) := by
      rwa [S.ker_boundaryMap_eq_liftedBoundaryIdeal I]
    have hquot := RingHom.mem_ker.mp hk
    have : Ideal.Quotient.mk I b = 0 := by
      simpa [boundaryMap] using hquot
    exact (Ideal.Quotient.eq_zero_iff_mem).mp this

end Retraction

end

end SplitRetractionBoundaryQuotient
end Experimental
end PCRLean
