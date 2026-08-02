import Mathlib
import PCRLean.BlockMatrixStableSubmodule
import PCRLean.EndomorphismGeneration

/-!
# Passive-module Hasse--Morita descent

A finite Hasse packet acting on the Frobenius-coordinate factor can be lifted
fibrewise to a module with arbitrary passive rows.  If the original packet
generates all matrix units on the Frobenius factor, the lifted packet generates
all left matrix units.  Stability of a passive submodule under the lifted
packet therefore forces a Morita decomposition from one submodule of the
passive row module.

This is the module-valued counterpart of ideal Frobenius descent.  It provides
a precise route for transporting passive relation modules and conormal data to
the Frobenius base rather than assuming passive safety from active
permissibility.
-/

namespace PCRLean
namespace PassiveHasseMoritaDescent

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {ι : Type v} {μ : Type w} {κ : Type x}
variable [Fintype ι] [DecidableEq ι]

abbrev Coordinates := ι → R
abbrev ProductCoordinates := (ι × μ) → R

/-- Lift an endomorphism of the Frobenius coordinate factor to every passive
row. -/
def liftLeft
    (T : Module.End R (Coordinates (R := R) (ι := ι))) :
    Module.End R (ProductCoordinates (R := R) (ι := ι) (μ := μ)) where
  toFun f p := T (fun i => f (i, p.2)) p.1
  map_add' := by
    intro f g
    funext p
    change T ((fun i => f (i, p.2)) + (fun i => g (i, p.2))) p.1 =
      (T (fun i => f (i, p.2)) + T (fun i => g (i, p.2))) p.1
    exact congrFun (T.map_add
      (fun i => f (i, p.2)) (fun i => g (i, p.2))) p.1
  map_smul' := by
    intro a f
    funext p
    change T (a • (fun i => f (i, p.2))) p.1 =
      (a • T (fun i => f (i, p.2))) p.1
    exact congrFun (T.map_smul a (fun i => f (i, p.2))) p.1

@[simp] theorem liftLeft_zero :
    liftLeft (R := R) (ι := ι) (μ := μ) 0 = 0 := by
  apply LinearMap.ext
  intro f
  funext p
  rfl

@[simp] theorem liftLeft_id :
    liftLeft (R := R) (ι := ι) (μ := μ)
      (LinearMap.id : Module.End R (Coordinates (R := R) (ι := ι))) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext p
  rfl

@[simp] theorem liftLeft_add
    (S T : Module.End R (Coordinates (R := R) (ι := ι))) :
    liftLeft (μ := μ) (S + T) = liftLeft (μ := μ) S + liftLeft (μ := μ) T := by
  apply LinearMap.ext
  intro f
  funext p
  rfl

@[simp] theorem liftLeft_smul
    (a : R) (T : Module.End R (Coordinates (R := R) (ι := ι))) :
    liftLeft (μ := μ) (a • T) = a • liftLeft (μ := μ) T := by
  apply LinearMap.ext
  intro f
  funext p
  rfl

@[simp] theorem liftLeft_comp
    (S T : Module.End R (Coordinates (R := R) (ι := ι))) :
    liftLeft (μ := μ) (S.comp T) =
      (liftLeft (μ := μ) S).comp (liftLeft (μ := μ) T) := by
  apply LinearMap.ext
  intro f
  funext p
  rfl

/-- Fibrewise lift of an operator packet. -/
def liftedPacket
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι))) :
    κ → Module.End R (ProductCoordinates (R := R) (ι := ι) (μ := μ)) :=
  fun k => liftLeft (μ := μ) (ops k)

/-- Generated operator expressions remain generated after fibrewise lifting. -/
theorem generated_liftLeft
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    {T : Module.End R (Coordinates (R := R) (ι := ι))}
    (hT : EndomorphismGeneration.Generated ops T) :
    EndomorphismGeneration.Generated (liftedPacket (μ := μ) ops)
      (liftLeft (μ := μ) T) := by
  induction hT with
  | zero =>
      simpa using
        (EndomorphismGeneration.Generated.zero
          (ops := liftedPacket (μ := μ) ops))
  | identity =>
      simpa using
        (EndomorphismGeneration.Generated.identity
          (ops := liftedPacket (μ := μ) ops))
  | generator k =>
      exact EndomorphismGeneration.Generated.generator
        (ops := liftedPacket (μ := μ) ops) k
  | add hS hT ihS ihT =>
      simpa using EndomorphismGeneration.Generated.add ihS ihT
  | smul a hT ihT =>
      simpa using EndomorphismGeneration.Generated.smul a ihT
  | comp hS hT ihS ihT =>
      simpa using EndomorphismGeneration.Generated.comp ihS ihT

/-- A lifted coordinate matrix unit is the corresponding left block matrix
unit. -/
theorem liftLeft_matrixUnit
    (i j : ι) :
    liftLeft (μ := μ)
      (MatrixStableSubmodule.matrixUnit (R := R) i j) =
      BlockMatrixStableSubmodule.leftMatrixUnit
        (R := R) (μ := μ) i j := by
  apply LinearMap.ext
  intro f
  funext p
  rcases p with ⟨a, m⟩
  by_cases h : a = i
  · subst a
    simp [liftLeft, MatrixStableSubmodule.matrixUnit_apply,
      BlockMatrixStableSubmodule.leftMatrixUnit_apply]
  · simp [liftLeft, MatrixStableSubmodule.matrixUnit_apply,
      BlockMatrixStableSubmodule.leftMatrixUnit_apply, h]

/-- Matrix-unit generation on the Frobenius factor becomes left-matrix-unit
generation on arbitrary passive rows. -/
theorem liftedPacket_generatesLeftMatrixUnits
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits ops) :
    ∀ i j,
      EndomorphismGeneration.Generated (liftedPacket (μ := μ) ops)
        (BlockMatrixStableSubmodule.leftMatrixUnit
          (R := R) (μ := μ) i j) := by
  intro i j
  have h := generated_liftLeft (μ := μ) ops (hgen i j)
  simpa [liftLeft_matrixUnit (R := R) (μ := μ) i j] using h

/-- Stability under a matrix-unit-generating packet on the Frobenius factor
forces full left-block invariance of the passive submodule. -/
theorem leftInvariant_of_liftedPacket_stable
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits ops)
    (N : Submodule R (ProductCoordinates (R := R) (ι := ι) (μ := μ)))
    (hstable : ∀ k,
      EndomorphismGeneration.StableUnder N (liftedPacket (μ := μ) ops k)) :
    BlockMatrixStableSubmodule.LeftInvariant N := by
  intro i j x hx
  exact EndomorphismGeneration.stable_of_generated
    (liftedPacket (μ := μ) ops) N hstable
    (liftedPacket_generatesLeftMatrixUnits (μ := μ) ops hgen i j) x hx

/-- Passive Morita descent: a packet-stable submodule is the extension of one
submodule of the passive row module. -/
theorem eq_fromRowModule_of_liftedPacket_stable
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits ops)
    (N : Submodule R (ProductCoordinates (R := R) (ι := ι) (μ := μ)))
    (hstable : ∀ k,
      EndomorphismGeneration.StableUnder N (liftedPacket (μ := μ) ops k)) :
    N = BlockMatrixStableSubmodule.fromRowModule (ι := ι)
      (BlockMatrixStableSubmodule.rowModule N) := by
  exact BlockMatrixStableSubmodule.eq_fromRowModule N
    (leftInvariant_of_liftedPacket_stable ops hgen N hstable)

end

end PassiveHasseMoritaDescent
end PCRLean