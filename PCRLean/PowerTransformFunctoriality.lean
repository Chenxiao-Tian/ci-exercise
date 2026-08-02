import Mathlib

/-!
# Power functoriality of controlled transforms

Controlled transforms of Frobenius powers do not require coordinate-specific
calculations.  If a chart homomorphism factors a root equation as

`φ(f) = E^b * f'`,

then the same chart factors its `q`-th power as

`φ(f^q) = E^(b*q) * (f')^q`.

The statement is valid in every commutative ring and for every ring
homomorphism.  It is the algebraic recursion theorem allowing a centre word for
a lower-mark root packet to be reused for its Frobenius power at the multiplied
mark.
-/

namespace PCRLean
namespace PowerTransformFunctoriality

noncomputable section

universe u v

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- One controlled-transform factorization. -/
structure Factorization (φ : R →+* S) (E : S)
    (b : Nat) (f : R) where
  transform : S
  equation : φ f = E ^ b * transform

namespace Factorization

variable {φ : R →+* S} {E : S} {b : Nat} {f : R}
variable (F : Factorization φ E b f)

/-- Raising a controlled factorization to a power multiplies the exceptional
mark and raises the controlled transform to the same power. -/
def pow (q : Nat) : Factorization φ E (b * q) (f ^ q) where
  transform := F.transform ^ q
  equation := by
    calc
      φ (f ^ q) = (φ f) ^ q := by rw [map_pow]
      _ = (E ^ b * F.transform) ^ q := by rw [F.equation]
      _ = (E ^ b) ^ q * F.transform ^ q := by rw [mul_pow]
      _ = E ^ (b * q) * F.transform ^ q := by rw [pow_mul]

@[simp] theorem pow_transform (q : Nat) :
    (F.pow q).transform = F.transform ^ q := rfl

@[simp] theorem pow_equation (q : Nat) :
    φ (f ^ q) = E ^ (b * q) * (F.transform ^ q) :=
  (F.pow q).equation

/-- Iterated powering is multiplicative on the marked exponent. -/
theorem pow_pow (q r : Nat) :
    (F.pow q).pow r = F.pow (q * r) := by
  cases F
  simp [Factorization.pow, mul_assoc, pow_mul]

end Factorization

/-- Elementwise formulation without packaging. -/
theorem pow_factorization
    (φ : R →+* S) (E : S)
    {b q : Nat} {f g : R}
    (h : φ f = E ^ b * φ g) :
    φ (f ^ q) = E ^ (b * q) * φ (g ^ q) := by
  calc
    φ (f ^ q) = (φ f) ^ q := by rw [map_pow]
    _ = (E ^ b * φ g) ^ q := by rw [h]
    _ = E ^ (b * q) * (φ g) ^ q := by rw [mul_pow, pow_mul]
    _ = E ^ (b * q) * φ (g ^ q) := by rw [map_pow]

/-- Version whose controlled transform lives only in the target chart. -/
theorem pow_factorization_target
    (φ : R →+* S) (E : S)
    {b q : Nat} {f : R} {g : S}
    (h : φ f = E ^ b * g) :
    φ (f ^ q) = E ^ (b * q) * g ^ q :=
  (Factorization.mk g h).pow_equation q

/-- A finite packet of factorizations may be powered entrywise with one common
exceptional mark. -/
theorem finite_packet_pow
    {ι : Type*} [Fintype ι]
    (φ : R →+* S) (E : S)
    {b q : Nat} (f : ι → R) (g : ι → S)
    (h : ∀ i, φ (f i) = E ^ b * g i) :
    ∀ i, φ ((f i) ^ q) = E ^ (b * q) * (g i) ^ q :=
  fun i => pow_factorization_target φ E (h i)

end

end PowerTransformFunctoriality
end PCRLean
