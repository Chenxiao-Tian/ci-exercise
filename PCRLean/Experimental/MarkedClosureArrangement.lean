import Mathlib
import PCRLean.Experimental.OrderIdealMarkedClosureCompiler

/-!
# The intersection arrangement of marked correction closures

For a selected correction family `A`, write

`C_A = J ⊔ sup_{a ∈ A} component(a)`.

The scheme-theoretic intersection of the centres cut out by `C_A` and `C_B`
is cut out by `C_A ⊔ C_B`, which is exactly `C_{A ∪ B}`.  Since marked
acceptability is monotone under enlarging the centre ideal, every finite
intersection closure remains active-owner acceptable.  Thus nonunique
minimizers canonically generate a finite intersection semilattice rather than
forcing an arbitrary choice of one point.

This file proves only the ideal-theoretic and active-marked part.  Regularity,
clean intersection, passive Tor safety, boundary SNC, and ordinary blowup
serialization remain independent geometric gates.
-/

namespace PCRLean
namespace Experimental
namespace MarkedClosureArrangement

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {Component : Type v} [Fintype Component] [DecidableEq Component]
variable {Owner : Type w} [Fintype Owner]

open OrderIdealMarkedClosureCompiler

/-- Monotonicity of the closure ideal under adding correction components. -/
theorem closure_mono
    (J : Ideal R) (component : Component → Ideal R)
    {A B : Finset Component} (hAB : A ⊆ B) :
    closure J component A ≤ closure J component B := by
  rw [closure, closure]
  refine sup_le le_sup_left ?_
  refine Finset.sup_le ?_
  intro a ha
  exact le_sup_of_le_right (Finset.le_sup (hAB ha))

/-- Active marked acceptability is monotone under adding correction
components. -/
theorem acceptable_mono
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    {A B : Finset Component} (hAB : A ⊆ B)
    (hA : Acceptable J component Q A) :
    Acceptable J component Q B := by
  intro o
  exact (hA o).trans
    (pow_le_pow_left' (closure_mono J component hAB) _)

/-- Ideal cutting out the scheme-theoretic intersection of two marked closure
centres. -/
def intersectionClosure
    (J : Ideal R) (component : Component → Ideal R)
    (A B : Finset Component) : Ideal R :=
  closure J component (A ∪ B)

/-- The intersection closure is exactly the join of the two centre ideals. -/
theorem intersectionClosure_eq_sup
    (J : Ideal R) (component : Component → Ideal R)
    (A B : Finset Component) :
    intersectionClosure J component A B =
      closure J component A ⊔ closure J component B := by
  apply le_antisymm
  · rw [intersectionClosure, closure]
    refine sup_le ?_ ?_
    · exact (base_le_closure J component A).trans le_sup_left
    · refine Finset.sup_le ?_
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (component_le_closure J component A ha).trans le_sup_left
      · exact (component_le_closure J component B ha).trans le_sup_right
  · exact sup_le
      (closure_mono J component Finset.subset_union_left)
      (closure_mono J component Finset.subset_union_right)

/-- Either acceptable centre remains acceptable after passing to their
scheme-theoretic intersection. -/
theorem intersectionClosure_acceptable_left
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    {A B : Finset Component}
    (hA : Acceptable J component Q A) :
    Acceptable J component Q (A ∪ B) :=
  acceptable_mono J component Q Finset.subset_union_left hA

/-- Symmetric right-hand version. -/
theorem intersectionClosure_acceptable_right
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    {A B : Finset Component}
    (hB : Acceptable J component Q B) :
    Acceptable J component Q (A ∪ B) :=
  acceptable_mono J component Q Finset.subset_union_right hB

/-- Algebraic first-stage classification of a critical pair.  The `disjoint`
case means that the two centre ideals are comaximal, equivalently their
scheme-theoretic intersection is empty.  The `intersecting` case carries the
canonical intersection ideal for the later clean-intersection/Tor-excess gate. -/
inductive PairStatus
    (J : Ideal R) (component : Component → Ideal R)
    (A B : Finset Component) : Type (max u v)
  | same (h : A = B)
  | disjoint
      (hne : A ≠ B)
      (hcomax : intersectionClosure J component A B = ⊤)
  | intersecting
      (hne : A ≠ B)
      (hproper : intersectionClosure J component A B ≠ ⊤)

/-- Exact and choice-free coverage of the first critical-pair split. -/
noncomputable def classifyPair
    (J : Ideal R) (component : Component → Ideal R)
    (A B : Finset Component) :
    PairStatus J component A B := by
  classical
  by_cases hAB : A = B
  · exact PairStatus.same hAB
  · by_cases htop : intersectionClosure J component A B = ⊤
    · exact PairStatus.disjoint hAB htop
    · exact PairStatus.intersecting hAB htop

/-- In the disjoint branch the join of the two original centre ideals is the
unit ideal. -/
theorem sup_eq_top_of_disjoint
    (J : Ideal R) (component : Component → Ideal R)
    (A B : Finset Component)
    (h : intersectionClosure J component A B = ⊤) :
    closure J component A ⊔ closure J component B = ⊤ := by
  rw [← intersectionClosure_eq_sup J component A B]
  exact h

end

end MarkedClosureArrangement
end Experimental
end PCRLean
