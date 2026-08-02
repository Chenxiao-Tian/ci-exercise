import Mathlib
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Perfect

/-!
# Perfect-coefficient quasilinear forms are Frobenius powers

A diagonal `p^e`-quasilinear form over a perfect coefficient ring is the
`p^e`-th power of one linear form.  Thus a fully quasilinear initial form with
perfect coefficients carries no information beyond a cleaning translation.
The unresolved rank-zero chamber is therefore genuinely a relative/imperfect-
coefficient phenomenon; this theorem does not construct roots for functions
on an arbitrary smooth positive-dimensional base.
-/

namespace PCRLean.Algebra.PerfectQuasilinearRoot

variable {R : Type*} [CommRing R]
variable (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]

/-- The canonical `p^e`-th root supplied by inverse iterated Frobenius. -/
noncomputable def root (e : ℕ) (a : R) : R :=
  ((frobeniusEquiv R p).symm^[e]) a

/-- The canonical root really is a `p^e`-th root. -/
@[simp] theorem root_pow (e : ℕ) (a : R) :
    (root p e a) ^ (p ^ e) = a := by
  simpa [root] using
    (iterate_frobeniusEquiv_symm_pow_p_pow (R := R) p a e)

/-- The Frobenius exponent is positive because `p` is prime. -/
theorem charPow_pos (e : ℕ) : 0 < p ^ e := by
  exact pow_pos (Fact.out : p.Prime).pos e

/-- Frobenius powers distribute over a finite sum. -/
theorem finset_sum_pow_char_pow {ι : Type*} (s : Finset ι)
    (f : ι → R) (e : ℕ) :
    (∑ i ∈ s, f i) ^ (p ^ e) = ∑ i ∈ s, (f i) ^ (p ^ e) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [zero_pow (Nat.ne_of_gt (charPow_pos p e))]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [add_pow_char_pow, ih]

section Finite

variable {ι : Type*} [Fintype ι]

/-- A finite diagonal quasilinear form. -/
def diagonal (a x : ι → R) (e : ℕ) : R :=
  ∑ i, a i * x i ^ (p ^ e)

/-- Its canonical linear Frobenius root. -/
noncomputable def linearRoot (a x : ι → R) (e : ℕ) : R :=
  ∑ i, root p e (a i) * x i

/-- A diagonal quasilinear form over a perfect ring is one Frobenius power. -/
theorem linearRoot_pow (a x : ι → R) (e : ℕ) :
    (linearRoot p a x e) ^ (p ^ e) = diagonal p a x e := by
  classical
  unfold linearRoot diagonal
  rw [finset_sum_pow_char_pow (p := p) Finset.univ
    (fun i => root p e (a i) * x i) e]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, root_pow]

/-- Consequently the pure equation `y^(p^e) + diagonal(a,x)` is removed by
one cleaning translation `y ↦ y + linearRoot(a,x)`. -/
theorem cleaning_identity (a x : ι → R) (e : ℕ) (y : R) :
    (y + linearRoot p a x e) ^ (p ^ e) =
      y ^ (p ^ e) + diagonal p a x e := by
  rw [add_pow_char_pow, linearRoot_pow]

end Finite

end PCRLean.Algebra.PerfectQuasilinearRoot
