import Mathlib
import PCRLean.Experimental.IntrinsicKernelIdealFunctoriality
import PCRLean.Experimental.DualPacketRegularCentre
import PCRLean.Experimental.DualPacketRootPackage

/-!
# Experimental exact transport of dual-packet centres

Let a linear cotangent map carry the row span of one finite packet exactly onto
the row span of another.  The induced symmetric-algebra map then carries the
actual centre ideal exactly onto the new actual centre.  The same statement
holds simultaneously for every marked root-power package.

This is the correctly oriented affine overlap and hereditary transport theorem.
The geometric layer must still prove exact row-span transport for localization,
blowup charts, cleaning and reentry.
-/

namespace PCRLean
namespace Experimental
namespace DualPacketExactTransport

noncomputable section

universe u v₀ v₁ w₀ w₁

variable {K : Type u} [Field K]
variable {T₀ : Type v₀} {T₁ : Type v₁}
variable [AddCommGroup T₀] [Module K T₀]
variable [AddCommGroup T₁] [Module K T₁]
variable {ι : Type w₀} {κ : Type w₁}
variable [Fintype ι] [Fintype κ]

abbrev C₀ := Module.Dual K T₀
abbrev C₁ := Module.Dual K T₁

open IntrinsicKernelIdealFunctoriality
open DualPacketRegularCentre
open DualPacketRootPackage

/-- Exact row-span transport gives exact transport of the actual centre ideal. -/
theorem map_centreIdeal_eq
    (p : ι → C₀ (K := K) (T₀ := T₀))
    (r : κ → C₁ (K := K) (T₁ := T₁))
    (f : C₀ (K := K) (T₀ := T₀) →ₗ[K]
      C₁ (K := K) (T₁ := T₁))
    (hspan : (packetSpan p).map f = packetSpan r) :
    Ideal.map (symmetricMap f) (centreIdeal p) = centreIdeal r := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, centreIdeal, Ideal.span_le]
    rintro z ⟨s, rfl⟩
    rw [Ideal.mem_comap]
    rw [symmetricMap_ι]
    apply Ideal.subset_span
    refine ⟨⟨f s.1, ?_⟩, rfl⟩
    have hs : f s.1 ∈ (packetSpan p).map f := ⟨s.1, s.2, rfl⟩
    rw [hspan] at hs
    exact hs
  · rw [centreIdeal, Ideal.span_le]
    rintro z ⟨s, rfl⟩
    have hs : s.1 ∈ (packetSpan p).map f := by
      rw [hspan]
      exact s.2
    rcases hs with ⟨x, hx, hfx⟩
    have hgen :
        SymmetricAlgebra.ι K (C₀ (K := K) (T₀ := T₀)) x ∈
          centreIdeal p := by
      apply Ideal.subset_span
      exact ⟨⟨x, hx⟩, rfl⟩
    have hmapped := Ideal.mem_map_of_mem (symmetricMap f) hgen
    simpa [symmetricMap_ι, hfx] using hmapped

/-- Exact row-span transport gives exact transport of every marked root-power
package. -/
theorem map_rootPowerIdeal_eq
    (p : ι → C₀ (K := K) (T₀ := T₀))
    (r : κ → C₁ (K := K) (T₁ := T₁))
    (f : C₀ (K := K) (T₀ := T₀) →ₗ[K]
      C₁ (K := K) (T₁ := T₁))
    (hspan : (packetSpan p).map f = packetSpan r)
    (q : Nat) :
    Ideal.map (symmetricMap f) (rootPowerIdeal p q) =
      rootPowerIdeal r q := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, rootPowerIdeal, Ideal.span_le]
    rintro z ⟨s, rfl⟩
    rw [Ideal.mem_comap]
    change symmetricMap f
      ((SymmetricAlgebra.ι K (C₀ (K := K) (T₀ := T₀)) s.1) ^ q) ∈
        rootPowerIdeal r q
    rw [map_pow, symmetricMap_ι]
    apply Ideal.subset_span
    refine ⟨⟨f s.1, ?_⟩, rfl⟩
    have hs : f s.1 ∈ (packetSpan p).map f := ⟨s.1, s.2, rfl⟩
    rw [hspan] at hs
    exact hs
  · rw [rootPowerIdeal, Ideal.span_le]
    rintro z ⟨s, rfl⟩
    have hs : s.1 ∈ (packetSpan p).map f := by
      rw [hspan]
      exact s.2
    rcases hs with ⟨x, hx, hfx⟩
    have hgen :
        (SymmetricAlgebra.ι K (C₀ (K := K) (T₀ := T₀)) x) ^ q ∈
          rootPowerIdeal p q := by
      apply Ideal.subset_span
      exact ⟨⟨x, hx⟩, rfl⟩
    have hmapped := Ideal.mem_map_of_mem (symmetricMap f) hgen
    simpa [map_pow, symmetricMap_ι, hfx] using hmapped

/-- One exact row-span certificate simultaneously transports the actual centre
and the root package. -/
theorem map_centre_and_root_eq
    (p : ι → C₀ (K := K) (T₀ := T₀))
    (r : κ → C₁ (K := K) (T₁ := T₁))
    (f : C₀ (K := K) (T₀ := T₀) →ₗ[K]
      C₁ (K := K) (T₁ := T₁))
    (hspan : (packetSpan p).map f = packetSpan r)
    (q : Nat) :
    Ideal.map (symmetricMap f) (centreIdeal p) = centreIdeal r ∧
      Ideal.map (symmetricMap f) (rootPowerIdeal p q) =
        rootPowerIdeal r q :=
  ⟨map_centreIdeal_eq p r f hspan,
    map_rootPowerIdeal_eq p r f hspan q⟩

end

end DualPacketExactTransport
end Experimental
end PCRLean
