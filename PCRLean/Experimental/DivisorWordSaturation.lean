import Mathlib
import PCRLean.Experimental.PowerSaturationProduct

/-!
# Divisor-word saturation compiler

A finite Cartier trace word is represented algebraically by a list of
commuting exceptional equations.  Successively removing power torsion along
the equations is the same as one saturation by their product.  Hence the
saturated `H⁰` transform is independent of the ordering and parenthesization of
the divisor word.

The statement is deliberately module-theoretic.  The X041 scheme theorem must
supply the final exceptional Cartier equations, derived pullback, a uniform
power-torsion exponent, and the comparison with iterated strict transforms.
-/

namespace PCRLean
namespace Experimental
namespace DivisorWordSaturation

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open PowerSaturationProduct

/-- Successive saturation by a finite word of scalars. -/
def wordSaturation : List R → Submodule R M → Submodule R M
  | [], N => N
  | q :: qs, N => wordSaturation qs (powerSaturation q N)

/-- The product of an empty word acts trivially. -/
@[simp] theorem wordSaturation_nil (N : Submodule R M) :
    wordSaturation ([] : List R) N = N :=
  rfl

@[simp] theorem wordSaturation_cons
    (q : R) (qs : List R) (N : Submodule R M) :
    wordSaturation (q :: qs) N =
      wordSaturation qs (powerSaturation q N) :=
  rfl

/-- A finite word is equivalent to one saturation by its scalar product. -/
theorem wordSaturation_eq_prod
    (qs : List R) (N : Submodule R M) :
    wordSaturation qs N = powerSaturation qs.prod N := by
  induction qs generalizing N with
  | nil =>
      simp [wordSaturation]
  | cons q qs ih =>
      rw [wordSaturation_cons, ih]
      simpa [List.prod_cons] using
        (powerSaturation_mul q qs.prod N).symm

/-- Concatenating divisor words corresponds to successive saturation. -/
theorem wordSaturation_append
    (qs rs : List R) (N : Submodule R M) :
    wordSaturation (qs ++ rs) N =
      wordSaturation rs (wordSaturation qs N) := by
  induction qs generalizing N with
  | nil => simp [wordSaturation]
  | cons q qs ih =>
      simp only [List.cons_append, wordSaturation_cons]
      exact ih (powerSaturation q N)

/-- Permuting the divisor word does not change the saturated transform. -/
theorem wordSaturation_eq_of_perm
    {qs rs : List R} (hperm : qs.Perm rs) (N : Submodule R M) :
    wordSaturation qs N = wordSaturation rs N := by
  rw [wordSaturation_eq_prod, wordSaturation_eq_prod]
  exact congrArg (fun a : R => powerSaturation a N) hperm.prod_eq

/-- Reversing the divisor word has no effect. -/
theorem wordSaturation_reverse
    (qs : List R) (N : Submodule R M) :
    wordSaturation qs.reverse N = wordSaturation qs N := by
  apply wordSaturation_eq_of_perm
  have hreflexive : qs.reverse.Perm qs.reverse := List.Perm.refl _
  exact (List.perm_reverse).mp hreflexive

/-- Any two words with the same product define the same saturation. -/
theorem wordSaturation_eq_of_prod_eq
    {qs rs : List R} (h : qs.prod = rs.prod) (N : Submodule R M) :
    wordSaturation qs N = wordSaturation rs N := by
  rw [wordSaturation_eq_prod, wordSaturation_eq_prod, h]

end

end DivisorWordSaturation
end Experimental
end PCRLean
