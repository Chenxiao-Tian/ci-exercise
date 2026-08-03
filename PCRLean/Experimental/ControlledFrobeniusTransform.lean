import Mathlib

/-!
# Controlled transforms of Frobenius powers

The chart algebra of a permissible blowup has one elementary but important
feature. If the pullback of a root equation factors as

`φ(g) = E^m * g'`,

then the pullback of its `q`-th power factors with exactly the scaled mark:

`φ(g^q) = E^(q*m) * (g')^q`.

Thus, after dividing by the controlled exceptional factor, prime-power root
compression commutes exactly with every chart map. No preferred chart enters
the statement.

The theorem is deliberately ring-theoretic. A geometric application must
still construct every chart map, prove the factorization for every centre
component, establish quotient uniqueness where needed, and glue overlaps.
-/

namespace PCRLean
namespace Experimental
namespace ControlledFrobeniusTransform

noncomputable section

universe u v w

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

/-- Exact controlled-transform identity for one rooted equation. -/
theorem root_factorization
    (φ : A →+* B) (root : A) (E root' : B)
    (q mark : Nat)
    (hfactor : φ root = E ^ mark * root') :
    φ (root ^ q) = E ^ (q * mark) * (root' ^ q) := by
  rw [map_pow, hfactor, mul_pow, pow_mul]
  congr 1
  rw [Nat.mul_comm]

/-- A source equation explicitly identified with a power has the same
factorization. -/
theorem source_factorization
    (φ : A →+* B) (source root : A) (E root' : B)
    (q mark : Nat)
    (hsource : root ^ q = source)
    (hfactor : φ root = E ^ mark * root') :
    φ source = E ^ (q * mark) * (root' ^ q) := by
  rw [← hsource]
  exact root_factorization φ root E root' q mark hfactor

/-- Indexed families of rooted marked equations transform componentwise with
scaled marks. -/
theorem family_root_factorization
    {κ : Type w}
    (φ : A →+* B) (root : κ → A)
    (E : B) (root' : κ → B)
    (q : Nat) (mark : κ → Nat)
    (hfactor : ∀ i, φ (root i) = E ^ mark i * root' i) :
    ∀ i, φ ((root i) ^ q) =
      E ^ (q * mark i) * (root' i) ^ q := by
  intro i
  exact root_factorization φ (root i) E (root' i)
    q (mark i) (hfactor i)

/-- Dependent active-owner packets transform componentwise. -/
theorem multiOwner_root_factorization
    {Owner : Type w} {Row : Owner → Type*}
    (φ : A →+* B)
    (root : (o : Owner) → Row o → A)
    (E : B)
    (root' : (o : Owner) → Row o → B)
    (q : Nat)
    (mark : (o : Owner) → Row o → Nat)
    (hfactor : ∀ o i,
      φ (root o i) = E ^ mark o i * root' o i) :
    ∀ o i,
      φ ((root o i) ^ q) =
        E ^ (q * mark o i) * (root' o i) ^ q := by
  intro o i
  exact root_factorization φ (root o i) E (root' o i)
    q (mark o i) (hfactor o i)

/-- Owners may use different prime-power levels. -/
theorem multiOwner_variablePower_factorization
    {Owner : Type w} {Row : Owner → Type*}
    (φ : A →+* B)
    (root : (o : Owner) → Row o → A)
    (E : B)
    (root' : (o : Owner) → Row o → B)
    (power : (o : Owner) → Row o → Nat)
    (mark : (o : Owner) → Row o → Nat)
    (hfactor : ∀ o i,
      φ (root o i) = E ^ mark o i * root' o i) :
    ∀ o i,
      φ ((root o i) ^ power o i) =
        E ^ (power o i * mark o i) *
          (root' o i) ^ power o i := by
  intro o i
  exact root_factorization φ (root o i) E (root' o i)
    (power o i) (mark o i) (hfactor o i)

/-- If the controlled root becomes a unit, the controlled Frobenius equation is
also a unit. -/
theorem isUnit_pow_of_isUnit
    (q : Nat) {g : B} (hg : IsUnit g) : IsUnit (g ^ q) :=
  hg.pow q

end

end ControlledFrobeniusTransform
end Experimental
end PCRLean
