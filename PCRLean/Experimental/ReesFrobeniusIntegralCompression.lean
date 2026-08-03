import Mathlib
import PCRLean.ReesFoundation

/-!
# Frobenius roots as integral Rees-algebra compression

If a weighted equation is a prime-power Frobenius power, its lower-weight root
should not be interpreted as a blowup centre by itself. The correct structural
statement is that adjoining the root to the graded algebra is a finite integral
extension with the same ambient integral elements.

Let `x = g W^m` in the polynomial ring `A[W]`. If `x^p` already belongs to a
subalgebra `S`, then `x` is integral over `S`, since integrality descends from a
positive power. When `g^p = f`, the identity

`(g W^m)^p = f W^(mp)`

shows that a weighted Frobenius root is integral over every graded algebra
containing the original weighted equation. The algebra obtained by adjoining
this one root is finite over `S`. Moreover an ambient element is integral over
`S` if and only if it is integral over the root-adjoin algebra. Thus Frobenius
mark compression preserves the ambient integral closure and is not an identity
blowup.

A full resolution proof still needs the geometric theorem that this integral
equivalence preserves singular loci, permissible centres, controlled transforms
and hereditary reentry for differential Rees algebras.
-/

namespace PCRLean
namespace Experimental
namespace ReesFrobeniusIntegralCompression

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (p : Nat) [Fact p.Prime]

/-- Weighted element `a W^m`. -/
def weightedTerm (m : Nat) (a : A) : Polynomial A :=
  Polynomial.monomial m a

/-- Exact power identity for weighted terms. -/
theorem weightedTerm_pow (m : Nat) (a : A) :
    (weightedTerm m a) ^ p = weightedTerm (m * p) (a ^ p) := by
  exact Polynomial.monomial_pow m a p

/-- Any positive root of an element already lying in a subalgebra is integral
over that subalgebra. -/
theorem isIntegral_of_pow_mem
    (S : Subalgebra A (Polynomial A))
    (x : Polynomial A) (hx : x ^ p ∈ S) :
    IsIntegral S x := by
  have hpow : IsIntegral S (x ^ p) := by
    simpa using
      (isIntegral_algebraMap (R := S) (A := Polynomial A)
        (⟨x ^ p, hx⟩ : S))
  exact hpow.of_pow Fact.out.pos

/-- A weighted Frobenius root is integral over a graded algebra containing the
original weighted equation. -/
theorem weightedRoot_isIntegral
    (S : Subalgebra A (Polynomial A))
    (m : Nat) (f g : A)
    (hroot : g ^ p = f)
    (hsource : weightedTerm (m * p) f ∈ S) :
    IsIntegral S (weightedTerm m g) := by
  apply isIntegral_of_pow_mem p S (weightedTerm m g)
  rw [weightedTerm_pow, hroot]
  exact hsource

/-- Adjoining the one weighted root gives an integral algebra extension. -/
theorem rootAdjoin_isIntegral
    (S : Subalgebra A (Polynomial A))
    (m : Nat) (f g : A)
    (hroot : g ^ p = f)
    (hsource : weightedTerm (m * p) f ∈ S) :
    Algebra.IsIntegral S
      (Algebra.adjoin S {weightedTerm m g}) := by
  apply Algebra.IsIntegral.adjoin
  intro x hx
  rcases hx with rfl
  exact weightedRoot_isIntegral p S m f g hroot hsource

/-- Adjoining one root is a finite-type algebra extension. -/
theorem rootAdjoin_finiteType
    (S : Subalgebra A (Polynomial A))
    (m : Nat) (g : A) :
    Algebra.FiniteType S
      (Algebra.adjoin S {weightedTerm m g}) := by
  exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton _)

/-- The root-adjoin extension is finite as a module. -/
theorem rootAdjoin_moduleFinite
    (S : Subalgebra A (Polynomial A))
    (m : Nat) (f g : A)
    (hroot : g ^ p = f)
    (hsource : weightedTerm (m * p) f ∈ S) :
    Module.Finite S (Algebra.adjoin S {weightedTerm m g}) := by
  exact Algebra.finite_adjoin_simple_of_isIntegral
    (weightedRoot_isIntegral p S m f g hroot hsource)

/-- Adjoining an integral weighted root does not change which ambient elements
are integral. This is the elementwise equality of the two ambient integral
closures. -/
theorem isIntegral_rootAdjoin_iff
    (S : Subalgebra A (Polynomial A))
    (m : Nat) (f g y : A)
    (hroot : g ^ p = f)
    (hsource : weightedTerm (m * p) f ∈ S) :
    IsIntegral S (Polynomial.C y) ↔
      IsIntegral (Algebra.adjoin S {weightedTerm m g}) (Polynomial.C y) := by
  let T := Algebra.adjoin S {weightedTerm m g}
  letI : Algebra.IsIntegral S T :=
    rootAdjoin_isIntegral p S m f g hroot hsource
  constructor
  · intro hy
    exact hy.tower_top
  · intro hy
    exact isIntegral_trans (Polynomial.C y) hy

/-- The same ambient integral-element equivalence for an arbitrary polynomial. -/
theorem isIntegralPolynomial_rootAdjoin_iff
    (S : Subalgebra A (Polynomial A))
    (m : Nat) (f g : A) (y : Polynomial A)
    (hroot : g ^ p = f)
    (hsource : weightedTerm (m * p) f ∈ S) :
    IsIntegral S y ↔
      IsIntegral (Algebra.adjoin S {weightedTerm m g}) y := by
  let T := Algebra.adjoin S {weightedTerm m g}
  letI : Algebra.IsIntegral S T :=
    rootAdjoin_isIntegral p S m f g hroot hsource
  constructor
  · intro hy
    exact hy.tower_top
  · intro hy
    exact isIntegral_trans y hy

/-- The root is integral over the algebra generated by the original weighted
Frobenius equation. -/
theorem weightedRoot_isIntegral_over_adjoin
    (m : Nat) (f g : A) (hroot : g ^ p = f) :
    IsIntegral
      (Algebra.adjoin A {weightedTerm (m * p) f})
      (weightedTerm m g) := by
  apply weightedRoot_isIntegral p
  exact Algebra.subset_adjoin rfl

/-- The root algebra is finite over the algebra generated by the original
weighted Frobenius equation. -/
theorem weightedRootAdjoin_moduleFinite
    (m : Nat) (f g : A) (hroot : g ^ p = f) :
    Module.Finite
      (Algebra.adjoin A {weightedTerm (m * p) f})
      (Algebra.adjoin
        (Algebra.adjoin A {weightedTerm (m * p) f})
        {weightedTerm m g}) := by
  exact Algebra.finite_adjoin_simple_of_isIntegral
    (weightedRoot_isIntegral_over_adjoin p m f g hroot)

/-- The same integrality statement for an iterated prime-power root. -/
theorem weightedIteratedRoot_isIntegral
    (e m : Nat) (f g : A)
    (hroot : g ^ (p ^ e) = f)
    (he : 0 < e) :
    IsIntegral
      (Algebra.adjoin A {weightedTerm (m * (p ^ e)) f})
      (weightedTerm m g) := by
  have hpowmem :
      (weightedTerm m g) ^ (p ^ e) ∈
        Algebra.adjoin A {weightedTerm (m * (p ^ e)) f} := by
    rw [Polynomial.monomial_pow, hroot]
    exact Algebra.subset_adjoin rfl
  have hint : IsIntegral
      (Algebra.adjoin A {weightedTerm (m * (p ^ e)) f})
      ((weightedTerm m g) ^ (p ^ e)) := by
    simpa using
      (isIntegral_algebraMap
        (R := Algebra.adjoin A {weightedTerm (m * (p ^ e)) f})
        (A := Polynomial A)
        (⟨(weightedTerm m g) ^ (p ^ e), hpowmem⟩ :
          Algebra.adjoin A {weightedTerm (m * (p ^ e)) f}))
  exact hint.of_pow (pow_pos Fact.out.pos e)

end

end ReesFrobeniusIntegralCompression
end Experimental
end PCRLean
