import Mathlib
import PCRLean.Algebra.FrobeniusMonomialPacket

/-!
# Canonical exponent quotient and residue packets

For a finite set of polynomial variables and a positive Frobenius scale `q`,
every exponent vector has the canonical coordinatewise division

`d = q • quotientExponent q d + residueExponent q d`.

Combining this identity with the rooted monomial theorem gives a canonical,
finite, exact Frobenius packet for every multivariate polynomial over a perfect
coefficient ring.  The packet is coordinate dependent but never truncates the
input and therefore avoids fixed-jet blindness.
-/

noncomputable section

namespace PCRLean.Algebra.FrobeniusCanonicalPacket

open MvPolynomial
namespace Packet := PCRLean.Algebra.FrobeniusMonomialPacket

variable {σ R : Type*}

/-- Coordinatewise exponent quotient. -/
def quotientExponent (q : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun n => n / q) (by simp)

/-- Coordinatewise exponent residue. -/
def residueExponent (q : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun n => n % q) (by simp)

@[simp] theorem quotientExponent_apply (q : ℕ) (d : σ →₀ ℕ) (i : σ) :
    quotientExponent q d i = d i / q := rfl

@[simp] theorem residueExponent_apply (q : ℕ) (d : σ →₀ ℕ) (i : σ) :
    residueExponent q d i = d i % q := rfl

/-- Exact coordinatewise Euclidean reconstruction. -/
theorem quotient_residue_reconstruct (q : ℕ) (d : σ →₀ ℕ) :
    q • quotientExponent q d + residueExponent q d = d := by
  ext i
  have h := Nat.div_add_mod (d i) q
  simpa [quotientExponent, residueExponent, Nat.mul_comm] using h

/-- Every residue coordinate is strictly below a positive packet scale. -/
theorem residueExponent_lt {q : ℕ} (hq : 0 < q) (d : σ →₀ ℕ) (i : σ) :
    residueExponent q d i < q := by
  simpa [residueExponent] using Nat.mod_lt (d i) hq

section Perfect

variable [CommRing R]
variable (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]

/-- Canonical finite exact Frobenius reconstruction of an arbitrary
multivariate polynomial. -/
theorem canonical_packet_reconstruction (e : ℕ) (f : MvPolynomial σ R) :
    (∑ d ∈ f.support,
      Packet.packetTerm p e
        (quotientExponent (p ^ e) d)
        (residueExponent (p ^ e) d)
        (coeff d f)) = f := by
  apply Packet.finite_packet_reconstruction p e f
    (quotientExponent (p ^ e)) (residueExponent (p ^ e))
  intro d hd
  exact quotient_residue_reconstruct (p ^ e) d

end Perfect

end PCRLean.Algebra.FrobeniusCanonicalPacket
