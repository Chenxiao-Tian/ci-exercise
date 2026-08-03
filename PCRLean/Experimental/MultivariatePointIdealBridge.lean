import Mathlib
import PCRLean.Experimental.MultivariateOrderIdealBridge

/-!
# Multivariate rational-point ideals and order transport

Translation by a rational point is a polynomial automorphism. It carries the
actual point ideal `(X_i-a_i)` to the actual origin ideal `(X_i)`. Hence the
support-order certificate for the translated equation transports back to an
actual power-containment certificate in the point ideal.

This upgrades the multivariate Frobenius order theorem from a semantic support
statement to marked permissibility along an explicit coherent affine centre at
an arbitrary rational point.

The centre here is a closed point, not the general positive-dimensional centre
needed by resolution. Regular-subspace centres, localization at arbitrary
scheme points, owner/passive legality and blowup transforms remain separate.
-/

namespace PCRLean
namespace Experimental
namespace MultivariatePointIdealBridge

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [DecidableEq σ]

open MultivariateFrobeniusOrderHeredity
open MultivariateOrderIdealBridge

/-- The coordinate equation of the point `a`. -/
def pointGenerator (a : σ → K) (i : σ) : MvPolynomial σ K :=
  MvPolynomial.X i - MvPolynomial.C (a i)

/-- Actual ideal of the rational point `a`. -/
def pointIdeal (a : σ → K) : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range (pointGenerator a))

@[simp] theorem translate_X (a : σ → K) (i : σ) :
    translate a (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (a i) := by
  simp [translate]

@[simp] theorem translate_C (a : σ → K) (c : K) :
    translate a (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [translate]

/-- Translation by `a` followed by translation by `-a` is the identity. -/
theorem translate_comp_neg (a : σ → K) :
    (translate a).comp (translate (-a)) =
      AlgHom.id K (MvPolynomial σ K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [translate]

/-- Translation by `-a` followed by translation by `a` is the identity. -/
theorem translate_neg_comp (a : σ → K) :
    (translate (-a)).comp (translate a) =
      AlgHom.id K (MvPolynomial σ K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [translate]

/-- Translation as a polynomial algebra automorphism. -/
noncomputable def translateEquiv (a : σ → K) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (translate a) (translate (-a))
    (translate_comp_neg a) (translate_neg_comp a)

/-- Every point equation belongs to the actual point ideal. -/
theorem pointGenerator_mem (a : σ → K) (i : σ) :
    pointGenerator a i ∈ pointIdeal a :=
  Ideal.subset_span ⟨i, rfl⟩

/-- Translation sends the point ideal exactly to the origin ideal. -/
theorem map_pointIdeal_eq_originIdeal (a : σ → K) :
    Ideal.map (translate a) (pointIdeal a) =
      originIdeal (K := K) (σ := σ) := by
  apply le_antisymm
  · rw [pointIdeal, originIdeal, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    simpa [pointGenerator, translate] using
      (X_mem_originIdeal (K := K) i)
  · rw [originIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem (translate a) (pointGenerator_mem a i)
    simpa [pointGenerator, translate] using hm

/-- Inverse translation sends the origin ideal exactly to the point ideal. -/
theorem map_originIdeal_eq_pointIdeal (a : σ → K) :
    Ideal.map (translate (-a)) (originIdeal (K := K) (σ := σ)) =
      pointIdeal a := by
  apply le_antisymm
  · rw [originIdeal, pointIdeal, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    simpa [pointGenerator, translate] using pointGenerator_mem a i
  · rw [pointIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem (translate (-a))
      (X_mem_originIdeal (K := K) i)
    simpa [pointGenerator, translate] using hm

/-- Translation carries every power of the point ideal to the matching power
of the origin ideal. -/
theorem map_pointIdeal_pow_eq_originIdeal_pow
    (a : σ → K) (mark : Nat) :
    Ideal.map (translate a) ((pointIdeal a) ^ mark) =
      (originIdeal (K := K) (σ := σ)) ^ mark := by
  rw [Ideal.map_pow, map_pointIdeal_eq_originIdeal]

/-- Inverse translation carries every origin-ideal power to the matching point
ideal power. -/
theorem map_originIdeal_pow_eq_pointIdeal_pow
    (a : σ → K) (mark : Nat) :
    Ideal.map (translate (-a))
        ((originIdeal (K := K) (σ := σ)) ^ mark) =
      (pointIdeal a) ^ mark := by
  rw [Ideal.map_pow, map_originIdeal_eq_pointIdeal]

/-- Exact membership transport between a point ideal and the origin ideal. -/
theorem mem_pointIdeal_pow_iff
    (a : σ → K) (f : MvPolynomial σ K) (mark : Nat) :
    f ∈ (pointIdeal a) ^ mark ↔
      translate a f ∈ (originIdeal (K := K) (σ := σ)) ^ mark := by
  constructor
  · intro hf
    have hm := Ideal.mem_map_of_mem (translate a) hf
    rw [map_pointIdeal_pow_eq_originIdeal_pow] at hm
    exact hm
  · intro hf
    have hm := Ideal.mem_map_of_mem (translate (-a)) hf
    rw [map_originIdeal_pow_eq_pointIdeal_pow] at hm
    have hvalue : translate (-a) (translate a f) = f := by
      have hcomp := congrArg
        (fun H : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => H f)
        (translate_neg_comp a)
      simpa [AlgHom.comp_apply] using hcomp
    rw [← hvalue]
    exact hm

/-- A pointwise support-order certificate gives actual marked-power containment
in the rational-point ideal. -/
theorem mem_pointIdeal_pow_of_atPointOrderGE
    (a : σ → K) (f : MvPolynomial σ K) (mark : Nat)
    (horder : AtPointOrderGE a f mark) :
    f ∈ (pointIdeal a) ^ mark := by
  apply (mem_pointIdeal_pow_iff a f mark).mpr
  exact mem_originIdeal_pow_of_orderGE (translate a f) mark horder

/-- A root order certificate therefore makes its prime-power equation
permissible for the actual rational-point ideal with the scaled mark. -/
theorem frobeniusPower_mem_pointIdeal_pow
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat) (a : σ → K) (g : MvPolynomial σ K)
    (hrootOrder : AtPointOrderGE a g mark) :
    g ^ (p ^ e) ∈ (pointIdeal a) ^ ((p ^ e) * mark) := by
  apply mem_pointIdeal_pow_of_atPointOrderGE
  exact (atPointOrderGE_power_iff p e mark a g).mpr hrootOrder

end

end MultivariatePointIdealBridge
end Experimental
end PCRLean
