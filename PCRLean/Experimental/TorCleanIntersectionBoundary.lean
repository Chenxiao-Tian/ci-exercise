import Mathlib
import PCRLean.Experimental.CriticalPairTorExcess

/-!
# Tor excess is not the clean-intersection gate

For ideals `I` and `J`, the equality `I inf J = I * J` is the familiar
first-Tor vanishing criterion for the two quotient modules.  It is useful for
passive tensor safety, but it is neither the definition nor a complete test of
clean geometric intersection.

The elementary self-pair calculation below already shows that the predicate is
not appropriate as a reflexive clean-intersection relation: a non-idempotent
regular centre intersects itself cleanly, whereas its self-pair is not
Tor-independent.  Conversely, tangent smooth curves can satisfy the ideal
intersection/product equality while their scheme-theoretic intersection is
nonreduced.  That geometric counterexample is retained in the X033 report and
machine audit.

The corrected wonderful-arrangement gate is regularity of every
scheme-theoretic intersection stratum, together with separate active, passive,
and boundary legality certificates.  Tor excess remains a separate passive
or derived-intersection diagnostic.
-/

namespace PCRLean
namespace Experimental
namespace TorCleanIntersectionBoundary

noncomputable section

universe u

variable {R : Type u} [CommRing R]

open CriticalPairTorExcess

/-- The self-pair Tor criterion is exactly idempotence of the ideal. -/
theorem torIndependent_self_iff_idempotent (I : Ideal R) :
    TorIndependent I I ↔ I = I * I := by
  rfl

/-- Every non-idempotent ideal fails the self-pair Tor criterion. -/
theorem not_torIndependent_self_of_not_idempotent
    (I : Ideal R) (hI : I ≠ I * I) :
    ¬ TorIndependent I I := by
  intro htor
  exact hI ((torIndependent_self_iff_idempotent I).mp htor)

/-- A proper nonzero principal Cartier ideal is a typical non-idempotent
boundary; whenever non-idempotence is supplied, it cannot satisfy the
self-pair Tor criterion. -/
theorem cartier_boundary_not_reflexive
    (I : Ideal R)
    (hproper : I ≠ ⊤)
    (hnonzero : I ≠ ⊥)
    (hnonidem : I ≠ I * I) :
    I ≠ ⊤ ∧ I ≠ ⊥ ∧ ¬ TorIndependent I I := by
  exact ⟨hproper, hnonzero,
    not_torIndependent_self_of_not_idempotent I hnonidem⟩

/-- Pairwise comaximal ideals remain in the Tor-independent chamber.  This is
precisely the algebra needed for disjoint-union layers, not a replacement for
regularity of nonempty intersection strata. -/
theorem torIndependent_of_disjoint
    (I J : Ideal R) (hIJ : I ⊔ J = ⊤) :
    TorIndependent I J := by
  exact (Ideal.mul_eq_inf_of_coprime hIJ).symm

end

end TorCleanIntersectionBoundary
end Experimental
end PCRLean
