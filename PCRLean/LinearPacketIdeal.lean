import Mathlib
import PCRLean.ActualIdealGluing

/-!
# Actual ideals from finite linear trace packets

A finite packet of linear trace rows can be integrated into an actual ideal of
the affine polynomial ring by replacing each row with its linear polynomial.
Finite row operations do not change this ideal. Thus a local operator packet
whose frames differ by invertible row changes has a presentation-independent
actual linear ideal.

Regularity of the resulting centre requires a constant-rank/splitting theorem;
that is supplied separately at the linear-module level by
`SplitKernelCentre` and remains to be globalized over the scheme.
-/

namespace PCRLean
namespace LinearPacketIdeal

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ]
variable {τ : Type w} [Fintype τ]

/-- The linear polynomial attached to one coefficient row. -/
def linearPolynomial (a : σ → K) : MvPolynomial σ K :=
  ∑ i : σ, MvPolynomial.C (a i) * MvPolynomial.X i

/-- Linearity in the coefficient row. -/
theorem linearPolynomial_add (a b : σ → K) :
    linearPolynomial (fun i => a i + b i) =
      linearPolynomial a + linearPolynomial b := by
  classical
  simp [linearPolynomial, add_mul, Finset.sum_add_distrib]

/-- Scalar linearity in the coefficient row. -/
theorem linearPolynomial_smul (c : K) (a : σ → K) :
    linearPolynomial (fun i => c * a i) =
      MvPolynomial.C c * linearPolynomial a := by
  classical
  rw [linearPolynomial, linearPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_assoc]

/-- A finite row packet and its actual generated ideal. -/
def packetGenerator (packet : τ → σ → K) (t : τ) : MvPolynomial σ K :=
  linearPolynomial (packet t)

/-- The actual finite-type ideal cut out by the packet rows. -/
def packetIdeal (packet : τ → σ → K) : Ideal (MvPolynomial σ K) :=
  ActualIdealGluing.generatedIdeal (packetGenerator packet)

/-- Every packet row belongs to its actual ideal. -/
theorem generator_mem_packetIdeal (packet : τ → σ → K) (t : τ) :
    packetGenerator packet t ∈ packetIdeal packet :=
  ActualIdealGluing.generator_mem (packetGenerator packet) t

/-- A coefficient-row combination becomes the same combination of linear
polynomials. -/
theorem linearPolynomial_combination
    (packet : τ → σ → K) (coeff : τ → K) :
    linearPolynomial (fun i => ∑ t, coeff t * packet t i) =
      ∑ t, MvPolynomial.C (coeff t) * packetGenerator packet t := by
  classical
  simp only [linearPolynomial, packetGenerator]
  calc
    (∑ i : σ,
        MvPolynomial.C (∑ t : τ, coeff t * packet t i) *
          MvPolynomial.X i) =
        ∑ i : σ,
          (∑ t : τ, MvPolynomial.C (coeff t * packet t i)) *
            MvPolynomial.X i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_sum]
    _ = ∑ i : σ, ∑ t : τ,
          MvPolynomial.C (coeff t * packet t i) * MvPolynomial.X i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    _ = ∑ t : τ, ∑ i : σ,
          MvPolynomial.C (coeff t * packet t i) * MvPolynomial.X i := by
      rw [Finset.sum_comm]
    _ = ∑ t : τ, MvPolynomial.C (coeff t) *
          ∑ i : σ, MvPolynomial.C (packet t i) * MvPolynomial.X i := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [map_mul, mul_assoc]

/-- Explicit mutual row-combination certificates give equality of the actual
packet ideals. -/
theorem packetIdeal_eq_of_mutual_row_combinations
    (p q : τ → σ → K)
    (forward backward : τ → τ → K)
    (hforward : ∀ t i, p t i = ∑ u, forward t u * q u i)
    (hbackward : ∀ t i, q t i = ∑ u, backward t u * p u i) :
    packetIdeal p = packetIdeal q := by
  apply ActualIdealGluing.generatedIdeal_eq_of_mutual_combinations
    (packetGenerator p) (packetGenerator q)
    (fun t u => MvPolynomial.C (forward t u))
    (fun t u => MvPolynomial.C (backward t u))
  · intro t
    rw [packetGenerator]
    rw [← linearPolynomial_combination q (forward t)]
    apply congrArg linearPolynomial
    funext i
    exact hforward t i
  · intro t
    rw [packetGenerator]
    rw [← linearPolynomial_combination p (backward t)]
    apply congrArg linearPolynomial
    funext i
    exact hbackward t i

/-- A finite overlap certificate for linear packet frames. -/
structure FrameEquivalence (p q : τ → σ → K) where
  forward : τ → τ → K
  backward : τ → τ → K
  reconstruct_p : ∀ t i, p t i = ∑ u, forward t u * q u i
  reconstruct_q : ∀ t i, q t i = ∑ u, backward t u * p u i

/-- Equivalent packet frames define the same actual ideal. -/
theorem FrameEquivalence.ideal_eq
    {p q : τ → σ → K} (E : FrameEquivalence p q) :
    packetIdeal p = packetIdeal q := by
  rcases E with ⟨forward, backward, hp, hq⟩
  exact packetIdeal_eq_of_mutual_row_combinations
    p q forward backward hp hq

/-- The standard coordinate row at `i`. -/
def coordinateRow [DecidableEq σ] (i : σ) : σ → K :=
  fun j => if j = i then 1 else 0

/-- Its linear polynomial is the corresponding affine coordinate. -/
@[simp] theorem linearPolynomial_coordinateRow [DecidableEq σ] (i : σ) :
    linearPolynomial (coordinateRow (K := K) i) = MvPolynomial.X i := by
  classical
  rw [linearPolynomial]
  simp [coordinateRow]

/-- A coordinate packet gives the actual coordinate ideal. -/
theorem packetIdeal_coordinateRows [DecidableEq σ]
    (embed : τ → σ) :
    packetIdeal (fun t => coordinateRow (K := K) (embed t)) =
      Ideal.span (Set.range fun t : τ => MvPolynomial.X (embed t)) := by
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp [packetGenerator]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp [packetGenerator]⟩

end

end LinearPacketIdeal
end PCRLean