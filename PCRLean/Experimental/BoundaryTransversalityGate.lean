import Mathlib
import PCRLean.MarkedIdeal

/-!
# The ideal-theoretic boundary transversality gate

Regularity of two closed subschemes and of their scheme-theoretic intersection
does not imply that they meet transversely.  The minimal ideal-theoretic gate is

`I ⊓ J = I * J`.

For regular immersions this is the algebraic condition that the conormal
directions have no first-order overlap.  It is one indispensable part of SNC;
regularity, codimension additivity and local freeness remain additional gates.

The file also records the permanent no-go example `I = J = (X)`: all relevant
quotient rings are regular, but `I ⊓ I = I` whereas `I * I = I^2` and
`X ∉ I^2`.  Thus a regular quotient certificate may never be silently upgraded
to boundary transversality.
-/

namespace PCRLean
namespace Experimental
namespace BoundaryTransversalityGate

noncomputable section

universe u

variable {A : Type u} [CommRing A]

/-- Ideal-theoretic first-order transversality. -/
def Transverse (I J : Ideal A) : Prop :=
  I ⊓ J = I * J

/-- Transversality is symmetric in a commutative ring. -/
theorem transverse_comm (I J : Ideal A) :
    Transverse I J ↔ Transverse J I := by
  unfold Transverse
  rw [inf_comm, mul_comm]

/-- The square of a sum consists of the two pure squares and the mixed term. -/
theorem sup_square_decomposition (I J : Ideal A) :
    (I ⊔ J) ^ 2 = I ^ 2 ⊔ I * J ⊔ J ^ 2 := by
  rw [pow_two, sup_mul, mul_sup, mul_sup]
  rw [← pow_two, ← pow_two, mul_comm J I]
  ac_rfl

/-- Disjoint ideals are transverse. -/
theorem transverse_of_inf_eq_bot
    {I J : Ideal A} (h : I ⊓ J = ⊥) : Transverse I J := by
  unfold Transverse
  rw [h]
  apply le_antisymm bot_le
  rw [le_bot_iff]
  apply le_trans Ideal.mul_le_left
  exact le_inf le_rfl le_rfl

section Counterexample

/-- The coordinate ideal `(X)` in `ℤ[X]`. -/
def XIdeal : Ideal (Polynomial ℤ) :=
  Ideal.span {Polynomial.X}

/-- The generator belongs to the self-intersection but not to the product. -/
theorem X_mem_inf_not_mul :
    Polynomial.X ∈ XIdeal ⊓ XIdeal ∧
      Polynomial.X ∉ XIdeal * XIdeal := by
  constructor
  · exact ⟨Ideal.mem_span_singleton_self _, Ideal.mem_span_singleton_self _⟩
  · rw [XIdeal, Ideal.span_singleton_mul_span_singleton]
    simpa [pow_two] using
      MarkedIdeal.generator_support_not_square_span.2

/-- Permanent guard: a smooth divisor is not transverse to itself. -/
theorem XIdeal_not_self_transverse :
    ¬ Transverse XIdeal XIdeal := by
  intro h
  have hx : Polynomial.X ∈ XIdeal ⊓ XIdeal := X_mem_inf_not_mul.1
  rw [h] at hx
  exact X_mem_inf_not_mul.2 hx

end Counterexample

end

end BoundaryTransversalityGate
end Experimental
end PCRLean
