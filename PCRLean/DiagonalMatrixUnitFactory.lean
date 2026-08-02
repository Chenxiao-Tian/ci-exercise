import Mathlib
import PCRLean.EndomorphismGeneration

/-!
# Matrix units from separating diagonal operators

Let `R^ι` be a finite free coordinate module. Suppose a finite family of
diagonal operators has a coefficient matrix admitting an explicit left inverse:
for every target coordinate `d`, a finite linear combination of the diagonal
weights is the Kronecker delta at `d`. These combinations are the coordinate
projectors `E_{dd}`.

If the operator packet also contains transfer operators carrying the image of
`E_{jj}` to the `i`-th coordinate, then the packet generates every matrix unit
`E_{ij}` under addition, scalar multiplication and composition. The abstract
endomorphism-generation theorem can then turn stability under this finite
packet into Frobenius-base ideal descent.

For a one-variable Frobenius monomial frame, the diagonal operators are
`x^b H_b`; their weight matrix is the finite Pascal matrix. Its inverse is the
binomial-inversion matrix. Thus this file isolates the exact finite identity
needed from Hasse calculus.
-/

namespace PCRLean
namespace DiagonalMatrixUnitFactory

noncomputable section

universe u v w

variable {R : Type u} {ι : Type v} {β : Type w}
variable [CommRing R]
variable [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

abbrev Coordinates := ι → R

/-- A diagonal endomorphism with the declared coordinate weights. -/
def diagonal (weight : β → ι → R) (b : β) :
    Module.End R (Coordinates (R := R) (ι := ι)) where
  toFun x i := weight b i * x i
  map_add' := by
    intro x y
    ext i
    simp [mul_add]
  map_smul' := by
    intro r x
    ext i
    simp [mul_left_comm]

@[simp] theorem diagonal_apply
    (weight : β → ι → R) (b : β)
    (x : Coordinates (R := R) (ι := ι)) (i : ι) :
    diagonal weight b x i = weight b i * x i := rfl

/-- The packet consisting of diagonal generators and transfer generators. -/
def packet
    (weight : β → ι → R)
    (transfer : ι → ι → Module.End R (Coordinates (R := R) (ι := ι))) :
    (β ⊕ (ι × ι)) → Module.End R (Coordinates (R := R) (ι := ι))
  | Sum.inl b => diagonal weight b
  | Sum.inr ij => transfer ij.1 ij.2

/-- Finite sums of generated operators are generated. -/
theorem generated_sum
    {κ : Type*}
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (f : β → Module.End R (Coordinates (R := R) (ι := ι)))
    (hf : ∀ b, EndomorphismGeneration.Generated ops (f b)) :
    EndomorphismGeneration.Generated ops (∑ b, f b) := by
  classical
  induction (Finset.univ : Finset β) using Finset.induction_on with
  | empty =>
      simpa using (EndomorphismGeneration.Generated.zero (ops := ops))
  | @insert b s hb ih =>
      rw [Finset.sum_insert hb]
      exact EndomorphismGeneration.Generated.add (hf b) ih

/-- A left inverse for the weight matrix reconstructs each coordinate
projector as a finite linear combination of diagonal operators. -/
theorem projector_eq_sum
    (weight : β → ι → R) (coeff : ι → β → R)
    (hseparate : ∀ d i, ∑ b, coeff d b * weight b i =
      if i = d then 1 else 0)
    (d : ι) :
    MatrixStableSubmodule.matrixUnit (R := R) d d =
      ∑ b, coeff d b • diagonal weight b := by
  apply LinearMap.ext
  intro x
  funext i
  change (Pi.single d (x d)) i =
    ∑ b, coeff d b * (weight b i * x i)
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, hseparate d i]
  by_cases h : i = d
  · subst i
    simp
  · simp [h, ne_comm]

/-- The separating diagonal packet generates every diagonal matrix unit. -/
theorem generated_projector
    (weight : β → ι → R) (coeff : ι → β → R)
    (transfer : ι → ι → Module.End R (Coordinates (R := R) (ι := ι)))
    (hseparate : ∀ d i, ∑ b, coeff d b * weight b i =
      if i = d then 1 else 0)
    (d : ι) :
    EndomorphismGeneration.Generated (packet weight transfer)
      (MatrixStableSubmodule.matrixUnit (R := R) d d) := by
  rw [projector_eq_sum weight coeff hseparate d]
  apply generated_sum (packet weight transfer)
  intro b
  exact EndomorphismGeneration.Generated.smul (coeff d b)
    (EndomorphismGeneration.Generated.generator
      (ops := packet weight transfer) (Sum.inl b))

/-- A transfer certificate says that the transfer operator from `j` to `i`,
restricted to the `j`-th coordinate projector, is the matrix unit `E_{ij}`. -/
def TransferCertificate
    (transfer : ι → ι → Module.End R (Coordinates (R := R) (ι := ι))) : Prop :=
  ∀ i j,
    (transfer i j).comp (MatrixStableSubmodule.matrixUnit (R := R) j j) =
      MatrixStableSubmodule.matrixUnit (R := R) i j

/-- Separating diagonals together with certified transfers generate every
matrix unit. -/
theorem generatesMatrixUnits
    (weight : β → ι → R) (coeff : ι → β → R)
    (transfer : ι → ι → Module.End R (Coordinates (R := R) (ι := ι)))
    (hseparate : ∀ d i, ∑ b, coeff d b * weight b i =
      if i = d then 1 else 0)
    (htransfer : TransferCertificate (R := R) transfer) :
    EndomorphismGeneration.GeneratesMatrixUnits (packet weight transfer) := by
  intro i j
  have hmove := EndomorphismGeneration.Generated.generator
    (ops := packet weight transfer) (Sum.inr (i, j))
  have hproj := generated_projector weight coeff transfer hseparate j
  have hcomp := EndomorphismGeneration.Generated.comp hmove hproj
  simpa [packet, htransfer i j] using hcomp

/-- Stability under a separating diagonal-and-transfer packet forces full
endomorphism invariance of a coordinate submodule. -/
theorem fullyInvariant_of_stable
    (weight : β → ι → R) (coeff : ι → β → R)
    (transfer : ι → ι → Module.End R (Coordinates (R := R) (ι := ι)))
    (hseparate : ∀ d i, ∑ b, coeff d b * weight b i =
      if i = d then 1 else 0)
    (htransfer : TransferCertificate (R := R) transfer)
    (N : Submodule R (Coordinates (R := R) (ι := ι)))
    (hstable : ∀ k,
      EndomorphismGeneration.StableUnder N (packet weight transfer k)) :
    MatrixStableSubmodule.FullyInvariant N := by
  exact EndomorphismGeneration.fullyInvariant_of_generatesMatrixUnits
    (packet weight transfer) N
    (generatesMatrixUnits weight coeff transfer hseparate htransfer) hstable

end

end DiagonalMatrixUnitFactory
end PCRLean
