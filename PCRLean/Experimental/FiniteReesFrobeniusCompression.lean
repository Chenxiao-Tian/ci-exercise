import Mathlib
import PCRLean.Experimental.ReesFrobeniusIntegralCompression

/-!
# Finite Rees--Frobenius compression

A Noetherian or finitely presented differential Rees algebra carries finitely
many weighted equations.  If a finite subfamily consists of prime-characteristic
Frobenius powers `f_j = g_j^p`, all lower-weight roots may be adjoined at once.
Each root term is integral, the set of roots is finite, and the resulting
adjoin algebra is a finite integral extension.  It has exactly the same ambient
integral elements as the original graded algebra.

This is the finite-presentation form of Frobenius mark compression.  The
remaining geometric bridge is to prove that the corresponding integral
equivalence commutes with differential saturation and controlled transforms.
-/

namespace PCRLean
namespace Experimental
namespace FiniteReesFrobeniusCompression

noncomputable section

universe u v

variable {A : Type u} [CommRing A]
variable {κ : Type v} [Fintype κ]
variable (p : Nat) [Fact p.Prime]

open ReesFrobeniusIntegralCompression

/-- One finite weighted Frobenius presentation. -/
structure Presentation where
  weight : κ → Nat
  source : κ → A
  root : κ → A
  root_pow : ∀ j, (root j) ^ p = source j

namespace Presentation

variable (P : Presentation (A := A) (κ := κ) p)

/-- Named weighted source term. -/
def sourceTerm (j : κ) : Polynomial A :=
  weightedTerm (P.weight j * p) (P.source j)

/-- Named weighted root term. -/
def rootTerm (j : κ) : Polynomial A :=
  weightedTerm (P.weight j) (P.root j)

/-- Finite set of all root terms. -/
def rootSet : Set (Polynomial A) := Set.range P.rootTerm

/-- Every root term is integral over any graded algebra containing all named
source terms. -/
theorem rootTerm_isIntegral
    (S : Subalgebra A (Polynomial A))
    (hsource : ∀ j, P.sourceTerm j ∈ S)
    (j : κ) : IsIntegral S (P.rootTerm j) := by
  exact weightedRoot_isIntegral p S (P.weight j)
    (P.source j) (P.root j) (P.root_pow j) (hsource j)

/-- The finite root-adjoin algebra is integral over the source algebra. -/
theorem rootAdjoin_isIntegral
    (S : Subalgebra A (Polynomial A))
    (hsource : ∀ j, P.sourceTerm j ∈ S) :
    Algebra.IsIntegral S (Algebra.adjoin S P.rootSet) := by
  apply Algebra.IsIntegral.adjoin
  intro x hx
  rcases hx with ⟨j, rfl⟩
  exact P.rootTerm_isIntegral p S hsource j

/-- The set of root terms is finite. -/
theorem rootSet_finite : P.rootSet.Finite :=
  Set.finite_range P.rootTerm

/-- Adjoining the finite root packet gives a finite module extension. -/
theorem rootAdjoin_moduleFinite
    (S : Subalgebra A (Polynomial A))
    (hsource : ∀ j, P.sourceTerm j ∈ S) :
    Module.Finite S (Algebra.adjoin S P.rootSet) := by
  exact Algebra.finite_adjoin_of_finite_of_isIntegral
    P.rootSet_finite
    (fun x hx => by
      rcases hx with ⟨j, rfl⟩
      exact P.rootTerm_isIntegral p S hsource j)

/-- Finite Frobenius compression leaves the ambient integral elements
unchanged. -/
theorem isIntegral_rootAdjoin_iff
    (S : Subalgebra A (Polynomial A))
    (hsource : ∀ j, P.sourceTerm j ∈ S)
    (y : Polynomial A) :
    IsIntegral S y ↔ IsIntegral (Algebra.adjoin S P.rootSet) y := by
  let T := Algebra.adjoin S P.rootSet
  letI : Algebra.IsIntegral S T := P.rootAdjoin_isIntegral p S hsource
  constructor
  · intro hy
    exact hy.tower_top
  · intro hy
    exact isIntegral_trans y hy

/-- The finite root packet may equivalently be adjoined to the algebra generated
by the finite source packet itself. -/
def sourceAlgebra : Subalgebra A (Polynomial A) :=
  Algebra.adjoin A (Set.range P.sourceTerm)

/-- Every source term belongs to the generated source algebra. -/
theorem sourceTerm_mem_sourceAlgebra (j : κ) :
    P.sourceTerm j ∈ P.sourceAlgebra :=
  Algebra.subset_adjoin ⟨j, rfl⟩

/-- The finite root algebra is finite over the finite source algebra. -/
theorem rootAdjoin_over_sourceAlgebra_moduleFinite :
    Module.Finite P.sourceAlgebra
      (Algebra.adjoin P.sourceAlgebra P.rootSet) := by
  exact P.rootAdjoin_moduleFinite p P.sourceAlgebra
    P.sourceTerm_mem_sourceAlgebra

/-- Source and source-plus-root algebras have the same ambient integral
elements. -/
theorem isIntegral_sourceAlgebra_iff_rootAdjoin
    (y : Polynomial A) :
    IsIntegral P.sourceAlgebra y ↔
      IsIntegral (Algebra.adjoin P.sourceAlgebra P.rootSet) y :=
  P.isIntegral_rootAdjoin_iff p P.sourceAlgebra
    P.sourceTerm_mem_sourceAlgebra y

end Presentation

end

end FiniteReesFrobeniusCompression
end Experimental
end PCRLean
