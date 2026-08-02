import Mathlib
import PCRLean.PascalSeparation

/-!
# Finite Frobenius--Hasse model

Fix `q > 0` and a commutative base ring `R`. On the free module with basis
`1,x,...,x^(q-1)`, define multiplication by `x^a` using the monogenic relation
`x^q = t`, and define the Hasse operator `H_b` by

`H_b(x^c) = choose(c,b) x^(c-b)`.

The composites `x^b H_b` are the Pascal diagonal operators. Finite Pascal
separation therefore produces every coordinate projector. Moreover
`x^i H_j E_{jj} = E_{ij}`. It follows that the primitive finite packet
consisting only of multiplication operators and Hasse operators generates the
full endomorphism algebra.

This is the explicit finite algebraic core of the local identity
`D_A^(e) = End_(A^(p^e))(A)` on a one-variable Frobenius frame. The next
geometric step is to transport this model to actual polynomial or etale
Frobenius charts and tensor the construction across several variables.
-/

namespace PCRLean
namespace FiniteHasseModel

noncomputable section

universe u

variable {R : Type u} [CommRing R]
variable (q : ℕ)

abbrev Coordinates := Fin q → R

/-- The standard coordinate vector. -/
def basisVector (j : Fin q) : Coordinates (R := R) q :=
  Pi.single j 1

/-- A linear map defined by prescribing the image of every standard coordinate
vector. -/
def fromBasisImages
    (image : Fin q → Coordinates (R := R) q) :
    Module.End R (Coordinates (R := R) q) where
  toFun x := ∑ j, x j • image j
  map_add' := by
    intro x y
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    simp [Finset.smul_sum, mul_smul]

@[simp] theorem fromBasisImages_basisVector
    (image : Fin q → Coordinates (R := R) q) (j : Fin q) :
    fromBasisImages q image (basisVector (R := R) q j) = image j := by
  classical
  simp [fromBasisImages, basisVector]

/-- A single coordinate vector with arbitrary coefficient is a scalar multiple
of the standard basis vector. -/
theorem single_eq_smul_basisVector
    (x : Coordinates (R := R) q) (j : Fin q) :
    Pi.single j (x j) = x j • basisVector (R := R) q j := by
  ext i
  by_cases h : i = j
  · subst i
    simp [basisVector]
  · simp [basisVector, h]

/-- Endomorphisms of the coordinate module are determined by their values on
standard coordinate vectors. -/
theorem end_ext_basis
    {S T : Module.End R (Coordinates (R := R) q)}
    (h : ∀ j, S (basisVector (R := R) q j) =
      T (basisVector (R := R) q j)) :
    S = T := by
  apply LinearMap.ext
  intro x
  have hsum : (∑ j, Pi.single j (x j)) = x :=
    LinearMap.sum_single_apply (fun _ : Fin q => R) x
  rw [← hsum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [single_eq_smul_basisVector (R := R) q x j,
    map_smul, map_smul, h j]

/-- The image of `x^c` under the Hasse operator of order `b`. -/
def hasseImage (b c : Fin q) : Coordinates (R := R) q :=
  if h : b.1 ≤ c.1 then
    (Nat.choose c.1 b.1 : R) •
      basisVector (R := R) q
        ⟨c.1 - b.1, lt_of_le_of_lt (Nat.sub_le _ _) c.2⟩
  else 0

/-- The finite Hasse operator of order `b`. -/
def hasse (b : Fin q) : Module.End R (Coordinates (R := R) q) :=
  fromBasisImages q (hasseImage (R := R) q b)

/-- Hasse action on one basis monomial when the order is admissible. -/
theorem hasse_basis_of_le (b c : Fin q) (h : b.1 ≤ c.1) :
    hasse (R := R) q b (basisVector (R := R) q c) =
      (Nat.choose c.1 b.1 : R) •
        basisVector (R := R) q
          ⟨c.1 - b.1, lt_of_le_of_lt (Nat.sub_le _ _) c.2⟩ := by
  simp [hasse, hasseImage, h]

/-- Hasse action vanishes above the exponent. -/
theorem hasse_basis_of_lt (b c : Fin q) (h : c.1 < b.1) :
    hasse (R := R) q b (basisVector (R := R) q c) = 0 := by
  simp [hasse, hasseImage, Nat.not_le.mpr h]

/-- The top Hasse operator sends its matching monomial to the constant basis
vector. -/
theorem hasse_basis_self (b : Fin q) :
    hasse (R := R) q b (basisVector (R := R) q b) =
      basisVector (R := R) q
        ⟨0, Nat.zero_lt_of_lt b.2⟩ := by
  simpa using hasse_basis_of_le (R := R) q b b le_rfl

/-- The image of `x^c` under multiplication by `x^a` in the relation
`x^q = t`. Since `a,c < q`, at most one wrap occurs. -/
def multiplyImage (t : R) (a c : Fin q) : Coordinates (R := R) q :=
  if h : a.1 + c.1 < q then
    basisVector (R := R) q ⟨a.1 + c.1, h⟩
  else
    t • basisVector (R := R) q
      ⟨a.1 + c.1 - q, by omega⟩

/-- Multiplication by `x^a` on the finite monogenic Frobenius frame. -/
def multiply (t : R) (a : Fin q) :
    Module.End R (Coordinates (R := R) q) :=
  fromBasisImages q (multiplyImage (R := R) q t a)

/-- Multiplication on a basis monomial before the first wrap. -/
theorem multiply_basis_of_lt (t : R) (a c : Fin q)
    (h : a.1 + c.1 < q) :
    multiply (R := R) q t a (basisVector (R := R) q c) =
      basisVector (R := R) q ⟨a.1 + c.1, h⟩ := by
  simp [multiply, multiplyImage, h]

/-- Multiplication sends the constant basis vector to the corresponding
monomial basis vector. -/
theorem multiply_basis_zero (t : R) (a : Fin q) :
    multiply (R := R) q t a
      (basisVector (R := R) q
        ⟨0, Nat.zero_lt_of_lt a.2⟩) =
        basisVector (R := R) q a := by
  let z : Fin q := ⟨0, Nat.zero_lt_of_lt a.2⟩
  have hlt : a.1 + z.1 < q := by
    simpa [z] using a.2
  rw [multiply_basis_of_lt (R := R) q t a z hlt]
  congr

/-- The Hasse diagonal composite. -/
def diagonalHasse (t : R) (b : Fin q) :
    Module.End R (Coordinates (R := R) q) :=
  (multiply (R := R) q t b).comp (hasse (R := R) q b)

/-- On each basis monomial, `x^b H_b` acts by the Pascal weight. -/
theorem diagonalHasse_basis (t : R) (b c : Fin q) :
    diagonalHasse (R := R) q t b (basisVector (R := R) q c) =
      (Nat.choose c.1 b.1 : R) • basisVector (R := R) q c := by
  by_cases hbc : b.1 ≤ c.1
  · rw [diagonalHasse, LinearMap.comp_apply,
      hasse_basis_of_le (R := R) q b c hbc, map_smul]
    have hsum : b.1 + (c.1 - b.1) = c.1 :=
      Nat.add_sub_of_le hbc
    have hlt : b.1 + (c.1 - b.1) < q :=
      hsum ▸ c.2
    rw [multiply_basis_of_lt (R := R) q t b
      ⟨c.1 - b.1, lt_of_le_of_lt (Nat.sub_le _ _) c.2⟩ hlt]
    have hindex :
        (⟨b.1 + (c.1 - b.1), hlt⟩ : Fin q) = c := by
      apply Fin.ext
      exact hsum
    rw [hindex]
  · have hcb : c.1 < b.1 := Nat.lt_of_not_ge hbc
    have hchoose : Nat.choose c.1 b.1 = 0 :=
      Nat.choose_eq_zero_of_lt hcb
    rw [diagonalHasse, LinearMap.comp_apply,
      hasse_basis_of_lt (R := R) q b c hcb, map_zero]
    simp [hchoose]

/-- The abstract Pascal diagonal operator is exactly the concrete Hasse
composite. -/
theorem diagonalHasse_eq_pascalDiagonal (t : R) (b : Fin q) :
    diagonalHasse (R := R) q t b =
      DiagonalMatrixUnitFactory.diagonal
        (PascalSeparation.pascalWeight (R := R) q) b := by
  apply end_ext_basis (R := R) q
  intro c
  rw [diagonalHasse_basis (R := R) q t b c]
  ext i
  by_cases hic : i = c
  · subst i
    simp [basisVector, DiagonalMatrixUnitFactory.diagonal,
      PascalSeparation.pascalWeight]
  · simp [basisVector, DiagonalMatrixUnitFactory.diagonal,
      PascalSeparation.pascalWeight, hic]

/-- The transfer composite `x^i H_j`. -/
def transfer (t : R) (i j : Fin q) :
    Module.End R (Coordinates (R := R) q) :=
  (multiply (R := R) q t i).comp (hasse (R := R) q j)

/-- Matrix-unit action on a standard basis vector. -/
theorem matrixUnit_basis (i j c : Fin q) :
    MatrixStableSubmodule.matrixUnit (R := R) i j
      (basisVector (R := R) q c) =
        if c = j then basisVector (R := R) q i else 0 := by
  by_cases hcj : c = j
  · subst c
    ext k
    by_cases hki : k = i
    · subst k
      simp [basisVector, MatrixStableSubmodule.matrixUnit_apply]
    · simp [basisVector, MatrixStableSubmodule.matrixUnit_apply, hki]
  · have hjc : j ≠ c := by exact fun h => hcj h.symm
    ext k
    simp [basisVector, MatrixStableSubmodule.matrixUnit_apply, hcj, hjc]

/-- Restricting `x^i H_j` to the `j`-th projector gives `E_{ij}`. -/
theorem transfer_projector (t : R) (i j : Fin q) :
    (transfer (R := R) q t i j).comp
        (MatrixStableSubmodule.matrixUnit (R := R) j j) =
      MatrixStableSubmodule.matrixUnit (R := R) i j := by
  apply end_ext_basis (R := R) q
  intro c
  rw [LinearMap.comp_apply, matrixUnit_basis (R := R) q j j c]
  by_cases hcj : c = j
  · subst c
    simp only [if_pos rfl]
    rw [transfer, LinearMap.comp_apply,
      hasse_basis_self (R := R) q j,
      multiply_basis_zero (R := R) q t i,
      matrixUnit_basis (R := R) q i j j, if_pos rfl]
  · rw [if_neg hcj, map_zero,
      matrixUnit_basis (R := R) q i j c, if_neg hcj]

/-- Primitive finite packet: multiplication operators and Hasse operators only. -/
def primitivePacket (t : R) :
    (Fin q ⊕ Fin q) → Module.End R (Coordinates (R := R) q)
  | Sum.inl a => multiply (R := R) q t a
  | Sum.inr b => hasse (R := R) q b

/-- Replacing every generator by an expression in another packet transports all
generated expressions. -/
theorem generated_rebase
    {κ₁ κ₂ : Type*}
    (ops₁ : κ₁ → Module.End R (Coordinates (R := R) q))
    (ops₂ : κ₂ → Module.End R (Coordinates (R := R) q))
    (hgen : ∀ k, EndomorphismGeneration.Generated ops₂ (ops₁ k))
    {T : Module.End R (Coordinates (R := R) q)}
    (hT : EndomorphismGeneration.Generated ops₁ T) :
    EndomorphismGeneration.Generated ops₂ T := by
  induction hT with
  | zero => exact EndomorphismGeneration.Generated.zero
  | identity => exact EndomorphismGeneration.Generated.identity
  | generator i => exact hgen i
  | add hS hT ihS ihT =>
      exact EndomorphismGeneration.Generated.add ihS ihT
  | smul r hT ihT =>
      exact EndomorphismGeneration.Generated.smul r ihT
  | comp hS hT ihS ihT =>
      exact EndomorphismGeneration.Generated.comp ihS ihT

/-- Every generator in the diagonal-and-transfer factory is generated by the
primitive multiplication/Hasse packet. -/
theorem factoryGenerator_generated (t : R)
    (k : Fin q ⊕ (Fin q × Fin q)) :
    EndomorphismGeneration.Generated (primitivePacket (R := R) q t)
      (DiagonalMatrixUnitFactory.packet
        (PascalSeparation.pascalWeight (R := R) q)
        (transfer (R := R) q t) k) := by
  cases k with
  | inl b =>
      change EndomorphismGeneration.Generated
        (primitivePacket (R := R) q t)
        (DiagonalMatrixUnitFactory.diagonal
          (PascalSeparation.pascalWeight (R := R) q) b)
      rw [← diagonalHasse_eq_pascalDiagonal (R := R) q t b]
      exact EndomorphismGeneration.Generated.comp
        (EndomorphismGeneration.Generated.generator
          (ops := primitivePacket (R := R) q t) (Sum.inl b))
        (EndomorphismGeneration.Generated.generator
          (ops := primitivePacket (R := R) q t) (Sum.inr b))
  | inr ij =>
      change EndomorphismGeneration.Generated
        (primitivePacket (R := R) q t)
        (transfer (R := R) q t ij.1 ij.2)
      exact EndomorphismGeneration.Generated.comp
        (EndomorphismGeneration.Generated.generator
          (ops := primitivePacket (R := R) q t) (Sum.inl ij.1))
        (EndomorphismGeneration.Generated.generator
          (ops := primitivePacket (R := R) q t) (Sum.inr ij.2))

/-- The primitive finite Frobenius--Hasse packet generates every coordinate
matrix unit. -/
theorem primitivePacket_generatesMatrixUnits (t : R) :
    EndomorphismGeneration.GeneratesMatrixUnits
      (primitivePacket (R := R) q t) := by
  intro i j
  have hfactory := DiagonalMatrixUnitFactory.generatesMatrixUnits
    (PascalSeparation.pascalWeight (R := R) q)
    (PascalSeparation.inverseCoeff (R := R) q)
    (transfer (R := R) q t)
    (PascalSeparation.pascalWeight_separates (R := R) q)
    (transfer_projector (R := R) q t) i j
  exact generated_rebase (R := R) q
    (DiagonalMatrixUnitFactory.packet
      (PascalSeparation.pascalWeight (R := R) q)
      (transfer (R := R) q t))
    (primitivePacket (R := R) q t)
    (factoryGenerator_generated (R := R) q t) hfactory

/-- Any coordinate submodule stable under multiplication and the finite Hasse
operators is fully invariant under all base-linear endomorphisms. -/
theorem fullyInvariant_of_primitive_stable
    (t : R) (N : Submodule R (Coordinates (R := R) q))
    (hstable : ∀ k,
      EndomorphismGeneration.StableUnder N
        (primitivePacket (R := R) q t k)) :
    MatrixStableSubmodule.FullyInvariant N := by
  exact EndomorphismGeneration.fullyInvariant_of_generatesMatrixUnits
    (primitivePacket (R := R) q t) N
    (primitivePacket_generatesMatrixUnits (R := R) q t) hstable

end

end FiniteHasseModel
end PCRLean
