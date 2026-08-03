import Mathlib
import PCRLean.Experimental.ReesFrobeniusIntegralCompression
import PCRLean.Experimental.FiniteReesFrobeniusCompression
import PCRLean.Experimental.FiniteHasseIntegralCompression

/-!
# Integral-equivalent Rees presentations

Resolution should not distinguish two finite graded presentations merely because
one contains lower-weight Frobenius roots or a finite Hasse root packet.  The
correct state is the equivalence class determined by ambient integral elements.

For subalgebras `S,T` of one ambient algebra `B`, define them to be integrally
equivalent when every ambient element is integral over `S` exactly when it is
integral over `T`.  This is an equivalence relation.  Single-root, finite-root,
and finite Hasse-compatible root adjoining all produce equivalent
presentations.

The relation is deliberately presentation-level.  The remaining geometric
bridge must prove that singular loci, legal centres, controlled transforms and
history data depend only on this equivalence class.
-/

namespace PCRLean
namespace Experimental
namespace IntegralEquivalentReesPresentations

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- Two presentations have the same ambient integral elements. -/
def IntegralEquivalent (S T : Subalgebra R B) : Prop :=
  ∀ y : B, IsIntegral S y ↔ IsIntegral T y

namespace IntegralEquivalent

/-- Reflexivity. -/
theorem refl (S : Subalgebra R B) : IntegralEquivalent S S :=
  fun _ => Iff.rfl

/-- Symmetry. -/
theorem symm {S T : Subalgebra R B}
    (h : IntegralEquivalent S T) : IntegralEquivalent T S :=
  fun y => (h y).symm

/-- Transitivity. -/
theorem trans {S T U : Subalgebra R B}
    (hST : IntegralEquivalent S T)
    (hTU : IntegralEquivalent T U) : IntegralEquivalent S U :=
  fun y => (hST y).trans (hTU y)

/-- Integral equivalence is unaffected by replacing the right presentation by
an equal subalgebra. -/
theorem congr_right {S T U : Subalgebra R B}
    (hST : IntegralEquivalent S T) (hTU : T = U) :
    IntegralEquivalent S U := by
  subst U
  exact hST

/-- Integral equivalence is unaffected by replacing the left presentation by
an equal subalgebra. -/
theorem congr_left {S T U : Subalgebra R B}
    (hST : IntegralEquivalent S T) (hSU : S = U) :
    IntegralEquivalent U T := by
  subst U
  exact hST

end IntegralEquivalent

section Polynomial

variable {A : Type w} [CommRing A]
variable (p : Nat) [Fact p.Prime]

open ReesFrobeniusIntegralCompression

/-- Adjoining one weighted Frobenius root gives an integrally equivalent
presentation. -/
theorem singleRoot_integralEquivalent
    (S : Subalgebra A (Polynomial A))
    (m : Nat) (f g : A)
    (hroot : g ^ p = f)
    (hsource : weightedTerm (m * p) f ∈ S) :
    IntegralEquivalent S (Algebra.adjoin S {weightedTerm m g}) :=
  fun y => isIntegralPolynomial_rootAdjoin_iff p S m f g y hroot hsource

end Polynomial

section FinitePolynomial

variable {A : Type w} [CommRing A]
variable {κ : Type x} [Fintype κ]
variable (p : Nat) [Fact p.Prime]

open FiniteReesFrobeniusCompression

/-- Adjoining a finite packet of weighted Frobenius roots gives an integrally
equivalent presentation. -/
theorem finiteRoot_integralEquivalent
    (P : Presentation (A := A) (κ := κ) p)
    (S : Subalgebra A (Polynomial A))
    (hsource : ∀ j, P.sourceTerm j ∈ S) :
    IntegralEquivalent S (Algebra.adjoin S P.rootSet) :=
  fun y => P.isIntegral_rootAdjoin_iff p S hsource y

/-- The canonical finite source algebra and its finite root extension are
integrally equivalent. -/
theorem finiteSourceRoot_integralEquivalent
    (P : Presentation (A := A) (κ := κ) p) :
    IntegralEquivalent P.sourceAlgebra
      (Algebra.adjoin P.sourceAlgebra P.rootSet) :=
  fun y => P.isIntegral_sourceAlgebra_iff_rootAdjoin p y

end FinitePolynomial

section FiniteHasse

variable {κ : Type w} [Fintype κ]
variable {δ : Type x} [Fintype δ]
variable (p : Nat) [Fact p.Prime]

open FiniteHasseIntegralCompression

/-- Adjoining a finite compatible root-Hasse packet preserves the integral
presentation class. -/
theorem finiteHasse_integralEquivalent
    (P : Packet (B := B) (κ := κ) (δ := δ) p)
    (S : Subalgebra R B)
    (hsource : ∀ d j, P.sourceOp d (P.source j) ∈ S) :
    IntegralEquivalent S (Algebra.adjoin S P.rootOperatorSet) :=
  fun y => P.isIntegral_rootOperatorAdjoin_iff p S hsource y

/-- The finite source-operator algebra and its root-operator extension are
integrally equivalent. -/
theorem finiteHasseSource_integralEquivalent
    (P : Packet (B := B) (κ := κ) (δ := δ) p) :
    IntegralEquivalent P.sourceOperatorAlgebra
      (Algebra.adjoin P.sourceOperatorAlgebra P.rootOperatorSet) :=
  fun y => P.isIntegral_sourceOperator_iff_rootOperatorAdjoin p y

end FiniteHasse

/-- A finite chain of presentation changes, every one of which preserves the
ambient integral class. -/
structure Chain (n : Nat) where
  presentation : Fin (n + 1) → Subalgebra R B
  adjacent : ∀ i : Fin n,
    IntegralEquivalent
      (presentation ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      (presentation ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

namespace Chain

variable {n : Nat} (C : Chain (R := R) (B := B) n)

/-- A finite chain of integral-equivalent rewrites has equivalent endpoints. -/
theorem endpoint_integralEquivalent :
    IntegralEquivalent (C.presentation 0)
      (C.presentation ⟨n, Nat.lt_succ_self n⟩) := by
  induction n with
  | zero => exact IntegralEquivalent.refl _
  | succ n ih =>
      let Cprefix : Chain (R := R) (B := B) n where
        presentation i := C.presentation ⟨i.1, lt_trans i.2 (Nat.lt_succ_self _)⟩
        adjacent i := C.adjacent i
      exact IntegralEquivalent.trans Cprefix.endpoint_integralEquivalent
        (C.adjacent ⟨n, Nat.lt_succ_self n⟩)

end Chain

end

end IntegralEquivalentReesPresentations
end Experimental
end PCRLean
