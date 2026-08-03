import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Expand

/-!
# Polynomial Hasse--Frobenius digit identity

For a polynomial over a ring of prime characteristic `p`, the `p*k`-th Hasse
derivative of a `p`-th power is the `p`-th power of the `k`-th Hasse derivative:

`D^[p*k](f^p) = (D^[k] f)^p`.

The proof avoids a separate Lucas-congruence development. Map `f` to a
polynomial ring over itself, Taylor-expand at the coefficient-ring variable,
and compare the coefficient of degree `p*k`. Frobenius expansion shows that
this coefficient is the `p`-th power of the degree-`k` Taylor coefficient.

This is the exact local operator identity required by finite Hasse integral
compression. Its multivariable version follows by iterating the one-variable
identity along coordinate Hasse operators.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialHasseFrobenius

noncomputable section

universe u v

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]
variable (p : Nat) [Fact p.Prime]

/-- Hasse differentiation commutes with coefficient maps. -/
theorem map_hasseDeriv
    (φ : R →+* S) (k : Nat) (f : Polynomial R) :
    (Polynomial.hasseDeriv k f).map φ =
      Polynomial.hasseDeriv k (f.map φ) := by
  ext n
  simp [Polynomial.hasseDeriv_coeff]

section Characteristic

variable [CharP R p]

/-- In characteristic `p`, the coefficient of degree `k*p` in a `p`-th power
is the `p`-th power of the coefficient of degree `k`. -/
theorem coeff_pow_prime_mul
    (f : Polynomial R) (k : Nat) :
    (f ^ p).coeff (k * p) = (f.coeff k) ^ p := by
  rw [← Polynomial.map_frobenius_expand (p := p) f]
  rw [Polynomial.coeff_map,
    Polynomial.coeff_expand_mul (Fact.out : p.Prime).pos]
  rw [frobenius_def]

end Characteristic

section Main

variable [CharP R p]

/-- Evaluating a polynomial with constant-polynomial coefficients at `X`
recovers the original polynomial. -/
theorem eval_X_map_C (f : Polynomial R) :
    (f.map (Polynomial.C : R →+* Polynomial R)).eval Polynomial.X = f := by
  simpa [Polynomial.eval] using
    (Polynomial.eval₂_C_X (p := f))

/-- Main one-variable Hasse--Frobenius compatibility theorem. -/
theorem hasseDeriv_pow_prime
    (f : Polynomial R) (k : Nat) :
    Polynomial.hasseDeriv (k * p) (f ^ p) =
      (Polynomial.hasseDeriv k f) ^ p := by
  let T := Polynomial R
  let F : Polynomial T := f.map (Polynomial.C : R →+* T)
  have ht := Polynomial.taylor_pow
    (r := (Polynomial.X : T)) (f := F) p
  have hc := congrArg
    (fun q : Polynomial T => q.coeff (k * p)) ht
  rw [Polynomial.taylor_coeff] at hc
  rw [coeff_pow_prime_mul p] at hc
  rw [Polynomial.taylor_coeff] at hc
  have hleft :
      (Polynomial.hasseDeriv (k * p) (F ^ p)).eval Polynomial.X =
        Polynomial.hasseDeriv (k * p) (f ^ p) := by
    have hpow : F ^ p = (f ^ p).map (Polynomial.C : R →+* T) := by
      simp [F]
    rw [hpow, ← map_hasseDeriv]
    exact eval_X_map_C _
  have hright :
      ((Polynomial.hasseDeriv k F).eval Polynomial.X) ^ p =
        (Polynomial.hasseDeriv k f) ^ p := by
    have heval :
        (Polynomial.hasseDeriv k F).eval Polynomial.X =
          Polynomial.hasseDeriv k f := by
      dsimp [F]
      rw [← map_hasseDeriv]
      exact eval_X_map_C _
    rw [heval]
  exact hleft.symm.trans (hc.trans hright)

/-- Iterated prime-power version. -/
theorem hasseDeriv_pow_primePower
    (e : Nat) (f : Polynomial R) (k : Nat) :
    Polynomial.hasseDeriv (k * (p ^ e)) (f ^ (p ^ e)) =
      (Polynomial.hasseDeriv k f) ^ (p ^ e) := by
  induction e with
  | zero => simp
  | succ e ih =>
      calc
        Polynomial.hasseDeriv (k * (p ^ (e + 1)))
            (f ^ (p ^ (e + 1))) =
          Polynomial.hasseDeriv ((k * p ^ e) * p)
            ((f ^ (p ^ e)) ^ p) := by
              rw [pow_succ, pow_mul]
              congr 2
              ring
        _ = (Polynomial.hasseDeriv (k * p ^ e)
              (f ^ (p ^ e))) ^ p :=
          hasseDeriv_pow_prime p (f ^ (p ^ e)) (k * p ^ e)
        _ = ((Polynomial.hasseDeriv k f) ^ (p ^ e)) ^ p := by
          rw [ih]
        _ = (Polynomial.hasseDeriv k f) ^ (p ^ (e + 1)) := by
          rw [pow_succ, pow_mul]

end Main

end

end PolynomialHasseFrobenius
end Experimental
end PCRLean
