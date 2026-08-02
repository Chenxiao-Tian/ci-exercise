import Mathlib
import PCRLean.FrobeniusRootCentre

/-!
# Split Frobenius root centres

The marked-power theorem for a Frobenius root ideal does not by itself exclude
the unit ideal.  A ring-theoretic retraction supplies the missing nonidentity
certificate.  If the root map `R → A` admits a ring-homomorphic left inverse,
then mapping an extended root ideal back along the retraction recovers the
original base ideal.  Hence a proper base core produces a proper actual root
centre.

This is the algebraic form of the local splitting available on a coordinate
Frobenius chart.  Regularity of the resulting centre still requires a
coordinate or conormal-frame certificate.
-/

namespace PCRLean
namespace SplitFrobeniusRootCentre

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- A Frobenius root section equipped with a ring-homomorphic retraction. -/
structure SplitRootSection (q : Nat)
    extends FrobeniusRootCentre.RootSection (R := R) (A := A) q where
  retract : A →+* R
  retract_root : retract.comp toRootSection.root = RingHom.id R

namespace SplitRootSection

variable {q : Nat}
variable (S : SplitRootSection (R := R) (A := A) q)

/-- The underlying actual root ideal. -/
def rootIdeal (J : Ideal R) : Ideal A :=
  S.toRootSection.rootIdeal J

/-- Mapping a root ideal back through the chosen retraction recovers its base
ideal exactly. -/
theorem rootIdeal_map_retract (J : Ideal R) :
    (S.rootIdeal J).map S.retract = J := by
  calc
    (S.rootIdeal J).map S.retract =
        (J.map S.toRootSection.root).map S.retract := rfl
    _ = J.map (S.retract.comp S.toRootSection.root) := by
      rw [Ideal.map_map]
    _ = J.map (RingHom.id R) := by
      rw [S.retract_root]
    _ = J := by
      exact Ideal.map_id J

/-- A split root map is injective. -/
theorem root_injective : Function.Injective S.toRootSection.root := by
  intro x y hxy
  have h := congrArg S.retract hxy
  simpa [show S.retract.comp S.toRootSection.root = RingHom.id R from
    S.retract_root] using h

/-- Proper base ideals give proper actual root ideals. -/
theorem rootIdeal_ne_top {J : Ideal R} (hJ : J ≠ ⊤) :
    S.rootIdeal J ≠ ⊤ := by
  intro htop
  have hmap := congrArg
    (fun I : Ideal A => I.map S.retract) htop
  have : J = ⊤ := by
    calc
      J = (S.rootIdeal J).map S.retract :=
        (S.rootIdeal_map_retract J).symm
      _ = (⊤ : Ideal A).map S.retract := by rw [htop]
      _ = ⊤ := by simp
  exact hJ this

/-- A proper descended marked packet therefore has a proper actual permissible
root centre. -/
theorem exists_proper_permissible_rootCentre
    {I : Ideal A} {J : Ideal R} (hq : 0 < q)
    (hI : I ≤ J.map (algebraMap R A))
    (hJ : J ≠ ⊤) :
    ∃ C : Ideal A,
      C ≠ ⊤ ∧
      FrobeniusRootCentre.RootSection.rootIdeal
        S.toRootSection J = C ∧
      MarkedIdeal.Permissible (R := A) ⟨I, q, hq⟩ C := by
  refine ⟨S.rootIdeal J, S.rootIdeal_ne_top hJ, rfl, ?_⟩
  exact S.toRootSection.markedPacket_permissible hq hI

/-- The same nonidentity conclusion applies when descent is an equality. -/
theorem exists_proper_permissible_rootCentre_of_eq
    {I : Ideal A} {J : Ideal R} (hq : 0 < q)
    (hI : I = J.map (algebraMap R A))
    (hJ : J ≠ ⊤) :
    ∃ C : Ideal A,
      C ≠ ⊤ ∧
      MarkedIdeal.Permissible (R := A) ⟨I, q, hq⟩ C := by
  obtain ⟨C, hC, hroot, hperm⟩ :=
    S.exists_proper_permissible_rootCentre hq (by simpa [hI]) hJ
  exact ⟨C, hC, hperm⟩

end SplitRootSection

end

end SplitFrobeniusRootCentre
end PCRLean
