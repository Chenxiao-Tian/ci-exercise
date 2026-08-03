import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Operations
import PCRLean.MarkedIdeal
import PCRLean.Experimental.FrobeniusNormalBasicOpenDescent

/-!
# Finite basic-open descent of marked permissibility

Let `s_i` generate the unit ideal and let `B_i = A[s_i⁻¹]`.  If on every basic
open chart the extended source ideal is contained in the marked power of the
extended centre,

`J B_i ≤ (C B_i)^m`,

then globally

`J ≤ C^m`.

The proof clears a chart-dependent power of `s_i` for each source element and
patches the resulting memberships using the unit-ideal cover.  Hence active
marked legality is a finite basic-open local property in exactly the form
needed by a Fitting-minor atlas.

This theorem does not descend passive Tor safety, normal flatness, regularity or
boundary SNC.  Those remain independent gates.
-/

namespace PCRLean
namespace Experimental
namespace MarkedPermissibilityBasicOpenDescent

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable {κ : Type v} [Fintype κ]
variable (s : κ → A)
variable (B : κ → Type w)
variable [∀ i, CommRing (B i)]
variable [∀ i, Algebra A (B i)]
variable [∀ i, IsLocalization (Submonoid.powers (s i)) (B i)]

open FrobeniusNormalBasicOpenDescent

/-- Marked-power containment descends from a finite basic-open cover. -/
theorem le_pow_of_basicOpenCover
    (source centre : Ideal A) (mark : Nat)
    (hcover : Ideal.span (Set.range s) = ⊤)
    (hlocal : ∀ i : κ,
      localIdeal s B source i ≤ (localIdeal s B centre i) ^ mark) :
    source ≤ centre ^ mark := by
  intro x hx
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (centre ^ mark) (Set.range s) hcover x
  rintro ⟨r, hr⟩
  rcases hr with ⟨i, rfl⟩
  have hxSource :
      algebraMap A (B i) x ∈ localIdeal s B source i :=
    Ideal.mem_map_of_mem (algebraMap A (B i)) hx
  have hxCentre :
      algebraMap A (B i) x ∈ (localIdeal s B centre i) ^ mark :=
    hlocal i hxSource
  have hxCentre' :
      algebraMap A (B i) x ∈ localIdeal s B (centre ^ mark) i := by
    rw [localIdeal_pow]
    exact hxCentre
  obtain ⟨n, hn⟩ :=
    exists_power_smul_mem_of_map_mem s B (centre ^ mark) i x hxCentre'
  refine ⟨n, ?_⟩
  simpa [smul_eq_mul] using hn

/-- Packet-level marked permissibility descends from the cover. -/
theorem permissible_of_basicOpenCover
    (P : MarkedIdeal.Packet A) (centre : Ideal A)
    (hcover : Ideal.span (Set.range s) = ⊤)
    (hlocal : ∀ i : κ,
      localIdeal s B P.ideal i ≤
        (localIdeal s B centre i) ^ P.mark) :
    MarkedIdeal.Permissible P centre :=
  le_pow_of_basicOpenCover s B P.ideal centre P.mark hcover hlocal

/-- A finite family of active owners may be checked chartwise and descended
simultaneously. -/
theorem owners_permissible_of_basicOpenCover
    {Owner : Type*}
    (P : Owner → MarkedIdeal.Packet A) (centre : Ideal A)
    (hcover : Ideal.span (Set.range s) = ⊤)
    (hlocal : ∀ i : κ, ∀ o : Owner,
      localIdeal s B (P o).ideal i ≤
        (localIdeal s B centre i) ^ (P o).mark) :
    ∀ o : Owner, MarkedIdeal.Permissible (P o) centre := by
  intro o
  exact permissible_of_basicOpenCover s B (P o) centre hcover
    (fun i => hlocal i o)

end

end MarkedPermissibilityBasicOpenDescent
end Experimental
end PCRLean
