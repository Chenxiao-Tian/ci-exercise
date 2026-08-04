import Mathlib
import PCRLean.Experimental.MarkedClosureArrangement

/-!
# The Tor-excess predicate for a pair of marked closure ideals

For ideals `I,J` in a commutative ring, the elementary ideal criterion

`I ∩ J = I * J`

is the vanishing condition corresponding to
`Tor₁^R(R/I,R/J) = 0`.  We isolate this criterion as the next obstruction gate
for two symmetry-related minimal centres.  The criterion is symmetric and
admits an exact choice-free split into a Tor-independent chamber and an excess
chamber.

No blowup-commutation theorem is asserted here.  Turning Tor independence,
clean intersection, and regularity of the scheme-theoretic intersection into a
wonderful ordinary-centre word is the load-bearing geometric edge.
-/

namespace PCRLean
namespace Experimental
namespace CriticalPairTorExcess

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

/-- Elementary Tor-independence criterion for two ideals. -/
def TorIndependent (I J : Ideal R) : Prop :=
  I ⊓ J = I * J

/-- Tor independence is symmetric. -/
theorem torIndependent_comm (I J : Ideal R) :
    TorIndependent I J ↔ TorIndependent J I := by
  simp [TorIndependent, inf_comm, mul_comm]

/-- Exact first obstruction split. -/
inductive ExcessStatus (I J : Ideal R) : Type u
  | independent (h : TorIndependent I J)
  | excess (h : ¬ TorIndependent I J)

/-- Choice-free compiler for the Tor-excess split. -/
noncomputable def classify (I J : Ideal R) : ExcessStatus I J := by
  classical
  by_cases h : TorIndependent I J
  · exact ExcessStatus.independent h
  · exact ExcessStatus.excess h

section MarkedClosures

variable {Component : Type v} [Fintype Component] [DecidableEq Component]

open OrderIdealMarkedClosureCompiler

/-- Tor-independence predicate for two marked closure centres. -/
def ClosureTorIndependent
    (J : Ideal R) (component : Component → Ideal R)
    (A B : Finset Component) : Prop :=
  TorIndependent (closure J component A) (closure J component B)

/-- Symmetry of the marked-closure critical-pair predicate. -/
theorem closureTorIndependent_comm
    (J : Ideal R) (component : Component → Ideal R)
    (A B : Finset Component) :
    ClosureTorIndependent J component A B ↔
      ClosureTorIndependent J component B A :=
  torIndependent_comm _ _

end MarkedClosures

end

end CriticalPairTorExcess
end Experimental
end PCRLean
