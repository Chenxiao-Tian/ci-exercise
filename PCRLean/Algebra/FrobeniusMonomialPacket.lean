import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import PCRLean.Algebra.PerfectQuasilinearRoot

noncomputable section

namespace PCRLean.Algebra.FrobeniusMonomialPacket

open MvPolynomial

variable {R σ : Type*} [CommRing R]
variable (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]

noncomputable def packetTerm (e : ℕ) (a r : σ →₀ ℕ) (c : R) :
    MvPolynomial σ R :=
  (monomial a (PCRLean.Algebra.PerfectQuasilinearRoot.root p e c)) ^ (p ^ e) *
    monomial r 1

theorem packetTerm_eq_monomial (e : ℕ) (a r : σ →₀ ℕ) (c : R) :
    packetTerm p e a r c = monomial ((p ^ e) • a + r) c := by
  unfold packetTerm
  rw [MvPolynomial.monomial_pow, MvPolynomial.monomial_mul]
  rw [PCRLean.Algebra.PerfectQuasilinearRoot.root_pow]
  simp

theorem finite_packet_reconstruction (e : ℕ) (f : MvPolynomial σ R)
    (quotient residue : (σ →₀ ℕ) → (σ →₀ ℕ))
    (hsplit : ∀ d ∈ f.support,
      (p ^ e) • quotient d + residue d = d) :
    (∑ d ∈ f.support,
      packetTerm p e (quotient d) (residue d) (coeff d f)) = f := by
  calc
    (∑ d ∈ f.support,
      packetTerm p e (quotient d) (residue d) (coeff d f)) =
        ∑ d ∈ f.support, monomial d (coeff d f) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [packetTerm_eq_monomial, hsplit d hd]
    _ = f := by
      simpa using f.as_sum.symm

end PCRLean.Algebra.FrobeniusMonomialPacket
