import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import PCRLean.Algebra.PerfectQuasilinearRoot

/-!
# Finite multivariate Frobenius monomial packets

Every monomial over a perfect characteristic-`p` coefficient ring admits an
exact `p^e`-root/residue factorization once its exponent has been split as

`d = p^e • a + r`.

Summing this identity over the finite support of a multivariate polynomial
gives a finite exact Frobenius packet.  The theorem is coordinate dependent,
but it has no bounded-jet loss and no unproved geometric content.
-/

noncomputable section

namespace PCRLean.Algebra.FrobeniusMonomialPacket

open MvPolynomial
namespace QRoot := PCRLean.Algebra.PerfectQuasilinearRoot

variable {R σ : Type*} [CommRing R]
variable (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]

/-- One rooted monomial multiplied by its residue monomial. -/
noncomputable def packetTerm (e : ℕ) (a r : σ →₀ ℕ) (c : R) :
    MvPolynomial σ R :=
  (monomial a (QRoot.root p e c)) ^ (p ^ e) * monomial r 1

/-- Exact rooted factorization of one monomial. -/
theorem packetTerm_eq_monomial (e : ℕ) (a r : σ →₀ ℕ) (c : R) :
    packetTerm p e a r c = monomial ((p ^ e) • a + r) c := by
  unfold packetTerm
  rw [monomial_pow, monomial_mul, QRoot.root_pow]
  simp

/-- A finite family of exponent splittings reconstructs the whole polynomial
exactly by summing the rooted packet terms over its support. -/
theorem finite_packet_reconstruction (e : ℕ) (f : MvPolynomial σ R)
    (quotient residue : (σ →₀ ℕ) → (σ →₀ ℕ))
    (hsplit : ∀ d ∈ f.support,
      (p ^ e) • quotient d + residue d = d) :
    (∑ d ∈ f.support,
      packetTerm p e (quotient d) (residue d) (coeff d f)) = f := by
  rw [← f.as_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [packetTerm_eq_monomial, hsplit d hd]

end PCRLean.Algebra.FrobeniusMonomialPacket
