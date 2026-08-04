import Mathlib
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import PCRLean.Experimental.FiniteProjectivePresentationDualFrame

/-!
# Automatic finite dual frames for finite projective modules

For a finite module `P`, `Module.Finite.exists_fin` supplies finitely many
generators `s : Fin n → P`.  Their `Fintype.linearCombination` map is a
surjection `(Fin n → R) →ₗ[R] P`.  If `P` is projective, this surjection splits.
The split presentation then produces the explicit finite dual frame constructed
in `FiniteProjectivePresentationDualFrame`.

This closes the purely algebraic finite-projective-to-dual-frame leaf of
D001/FND-11.  It does not construct the particular cokernel from an arbitrary
resolution state and it does not prove compatible geometric transport across
Fitting charts.
-/

namespace PCRLean
namespace Experimental
namespace FiniteProjectiveAutomaticDualFrame

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]

open FiniteProjectivePresentationDualFrame

/-- A finite module admits a surjection from a finite rank free module. -/
theorem exists_surjective_fin_fun
    [Module.Finite R P] :
    ∃ n : ℕ, ∃ project : (Fin n → R) →ₗ[R] P,
      Function.Surjective project := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := P)
  refine ⟨n, Fintype.linearCombination R s, ?_⟩
  exact
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R s).mp hs

/-- A finite projective module admits a split finite-free presentation. -/
theorem exists_splitFiniteFreePresentation
    [Module.Finite R P] [Module.Projective R P] :
    ∃ n : ℕ,
      Nonempty
        (SplitFiniteFreePresentation
          (R := R) (P := P) (ι := Fin n)) := by
  obtain ⟨n, project, hproject⟩ :=
    exists_surjective_fin_fun (R := R) (P := P)
  exact ⟨n, ⟨ofProjectiveSurjection project hproject⟩⟩

/-- A finite projective module admits an explicit finite dual frame. -/
theorem exists_finite_dualFrame
    [Module.Finite R P] [Module.Projective R P] :
    ∃ n : ℕ,
      Nonempty
        (ProjectiveMoritaDescent.DualFrame
          (R := R) (P := P) (ι := Fin n)) := by
  obtain ⟨n, F⟩ :=
    exists_splitFiniteFreePresentation (R := R) (P := P)
  exact ⟨n, ⟨F.some.toDualFrame⟩⟩

/-- Strong reconstruction form of the automatic finite dual-frame theorem. -/
theorem exists_finite_dualFrame_reconstruct
    [Module.Finite R P] [Module.Projective R P] :
    ∃ n : ℕ,
      ∃ F : ProjectiveMoritaDescent.DualFrame
        (R := R) (P := P) (ι := Fin n),
      ∀ x : P,
        (∑ i : Fin n, F.functional i x • F.vector i) = x := by
  obtain ⟨n, hF⟩ := exists_finite_dualFrame (R := R) (P := P)
  refine ⟨n, hF.some, ?_⟩
  intro x
  exact hF.some.reconstruct x

/-- Edge certificate recording both the finite free presentation and its
resulting dual frame at one common finite index. -/
structure AutomaticFrameCertificate
    [Module.Finite R P] [Module.Projective R P] where
  n : ℕ
  presentation :
    SplitFiniteFreePresentation (R := R) (P := P) (ι := Fin n)
  frame : ProjectiveMoritaDescent.DualFrame
    (R := R) (P := P) (ι := Fin n)
  frame_eq : frame = presentation.toDualFrame

/-- Construct the combined certificate. -/
noncomputable def automaticFrameCertificate
    [Module.Finite R P] [Module.Projective R P] :
    AutomaticFrameCertificate (R := R) (P := P) := by
  obtain ⟨n, hF⟩ :=
    exists_splitFiniteFreePresentation (R := R) (P := P)
  exact
    { n := n
      presentation := hF.some
      frame := hF.some.toDualFrame
      frame_eq := rfl }

end

end FiniteProjectiveAutomaticDualFrame
end Experimental
end PCRLean
