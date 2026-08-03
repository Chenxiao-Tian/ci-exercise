import Mathlib
import PCRLean.MultiOwnerHasseCore
import PCRLean.Experimental.DualPacketAffineQuotient
import PCRLean.Experimental.DualPacketAffineRootPackage
import PCRLean.Experimental.FrobeniusFiniteRootGeneration
import PCRLean.Experimental.DualPacketCoordinateNormalization

/-!
# Experimental rank-zero dual-packet no-go

If the cotangent row span of a finite packet has rank zero, then the row span is
zero.  Consequently the actual affine centre ideal, the full row-span root
package and every finite Frobenius packet-power ideal are all zero, and the
centre-basis pivot type is empty.

Thus the current linear packet cannot produce a nontrivial blowup centre in the
rank-zero chamber.  If a joint Hasse-core extension is identified with this
finite root ideal, every stable owner is also the zero ideal.  This is a typed
no-go theorem: progress in the rank-zero chamber requires an enriched
higher-Frobenius, radicial or nonlinear packet rather than repetition of the
same linear data.
-/

namespace PCRLean
namespace Experimental
namespace DualPacketRankZeroNoGo

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]
variable {κ : Type w} [Fintype κ]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))

open DualPacketRegularCentre
open DualPacketAffineLinearRealization
open DualPacketAffineRootPackage

/-- Rank zero forces the packet row span to be the zero submodule. -/
theorem packetSpan_eq_bot_of_finrank_eq_zero
    (packet : κ → Dual (K := K) (σ := σ))
    (hzero : FiniteDimensional.finrank K (packetSpan packet) = 0) :
    packetSpan packet = ⊥ := by
  have hsub : Subsingleton (packetSpan packet) :=
    FiniteDimensional.finrank_eq_zero.mp hzero
  apply le_antisymm
  · intro f hf
    change f = 0
    have heq : (⟨f, hf⟩ : packetSpan packet) = 0 :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val heq
  · exact bot_le

/-- Every named packet covector is zero in the rank-zero chamber. -/
theorem packet_eq_zero_of_finrank_eq_zero
    (packet : κ → Dual (K := K) (σ := σ))
    (hzero : FiniteDimensional.finrank K (packetSpan packet) = 0)
    (i : κ) : packet i = 0 := by
  have hi : packet i ∈ packetSpan packet :=
    Submodule.subset_span ⟨i, rfl⟩
  rw [packetSpan_eq_bot_of_finrank_eq_zero packet hzero] at hi
  simpa using hi

/-- The actual affine centre ideal is zero at rank zero. -/
theorem actualIdeal_eq_bot_of_finrank_eq_zero
    (packet : κ → Dual (K := K) (σ := σ))
    (hzero : FiniteDimensional.finrank K (packetSpan packet) = 0) :
    actualIdeal packet = ⊥ := by
  apply le_antisymm
  · rw [actualIdeal, Ideal.span_le]
    rintro z ⟨i, rfl⟩
    rw [packet_eq_zero_of_finrank_eq_zero packet hzero i]
    simp [FunctionalPacketIdeal.functionalPolynomial,
      FunctionalPacketIdeal.coefficientRow,
      LinearPacketIdeal.linearPolynomial]
  · exact bot_le

/-- The full row-span root package is zero at rank zero. -/
theorem actualRootPowerIdeal_eq_bot_of_finrank_eq_zero
    (packet : κ → Dual (K := K) (σ := σ))
    (hzero : FiniteDimensional.finrank K (packetSpan packet) = 0)
    (q : Nat) :
    actualRootPowerIdeal packet q = ⊥ := by
  have hspan := packetSpan_eq_bot_of_finrank_eq_zero packet hzero
  apply le_antisymm
  · rw [actualRootPowerIdeal, Ideal.span_le]
    rintro z ⟨f, rfl⟩
    have hf : f.1 = 0 := by
      have : f.1 ∈ (⊥ : Submodule K (Dual (K := K) (σ := σ))) := by
        rw [← hspan]
        exact f.2
      simpa using this
    rw [hf]
    by_cases hq : q = 0
    · subst q
      simp
    · simp [hq]
  · exact bot_le

section Frobenius

variable (p : Nat) [Fact p.Prime] [CharP K p]

/-- Every finite named packet-power ideal is zero at rank zero. -/
theorem packetPowerIdeal_eq_bot_of_finrank_eq_zero
    (packet : κ → Dual (K := K) (σ := σ))
    (hzero : FiniteDimensional.finrank K (packetSpan packet) = 0)
    (e : Nat) :
    FrobeniusFiniteRootGeneration.packetPowerIdeal p packet e = ⊥ := by
  rw [← FrobeniusFiniteRootGeneration.actualRootPowerIdeal_eq_packetPowerIdeal
    p packet e]
  exact actualRootPowerIdeal_eq_bot_of_finrank_eq_zero
    packet hzero (p ^ e)

/-- Rank zero has no pivot chart. -/
theorem centreIndex_isEmpty_of_finrank_eq_zero
    (packet : κ → Dual (K := K) (σ := σ))
    (hzero : FiniteDimensional.finrank K (packetSpan packet) = 0) :
    IsEmpty (DualPacketCoordinateNormalization.CentreIndex packet) := by
  change IsEmpty (Fin (FiniteDimensional.finrank K (packetSpan packet)))
  rw [hzero]
  infer_instance

end Frobenius

end

section Owners

universe uR uK uσ uκ uω

variable {R : Type uR} {K : Type uK}
variable [CommRing R] [Field K]
variable {σ : Type uσ} [Fintype σ] [DecidableEq σ]
variable {κ : Type uκ} [Fintype κ]
variable {ω : Type uω} [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}
variable (p : Nat) [Fact p.Prime] [CharP K p]

abbrev DirectionO := σ → K
abbrev DualO := Module.Dual K (DirectionO (K := K) (σ := σ))
abbrev AO := MvPolynomial σ K

variable [Algebra R (AO (K := K) (σ := σ))]

/-- Under finite-root realization, a rank-zero packet forces every stable owner
to be the zero ideal. -/
theorem owner_eq_bot_of_rank_zero_root_realization
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := AO (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (AO (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → DualO (K := K) (σ := σ))
    (hzero : FiniteDimensional.finrank K
      (DualPacketRegularCentre.packetSpan packet) = 0)
    (e : Nat)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (AO (K := K) (σ := σ))) =
        FrobeniusFiniteRootGeneration.packetPowerIdeal p packet e)
    (i : ω) : owners i = ⊥ := by
  apply le_antisymm
  · calc
      owners i ≤
          (MultiOwnerHasseCore.jointCore F owners).map
            (algebraMap R (AO (K := K) (σ := σ))) :=
        MultiOwnerHasseCore.owner_le_jointCoreExtension
          F owners hstable i
      _ = FrobeniusFiniteRootGeneration.packetPowerIdeal p packet e :=
        hsource
      _ = ⊥ :=
        packetPowerIdeal_eq_bot_of_finrank_eq_zero p packet hzero e
  · exact bot_le

end Owners

end DualPacketRankZeroNoGo
end Experimental
end PCRLean
