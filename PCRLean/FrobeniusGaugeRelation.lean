import Mathlib

/-!
# Frobenius gauge relations

Cleaning changes a presentation by adding an element in the image of a
Frobenius/root operator.  The invariant object is therefore not a chosen
representative but its coset modulo that image.  This file avoids any quotient
choice and proves directly that the gauge relation is an equivalence relation
preserved by every operator commuting with the gauge operator.
-/

namespace PCRLean
namespace FrobeniusGaugeRelation

noncomputable section

universe u v w

variable {R : Type u} {M : Type v} {ι : Type w}
variable [Ring R] [AddCommGroup M] [Module R M]

/-- Two presentations differ by a cleaning gauge term. -/
def GaugeEquivalent (F : Module.End R M) (x y : M) : Prop :=
  x - y ∈ LinearMap.range F

/-- Gauge equivalence is reflexive. -/
theorem refl (F : Module.End R M) (x : M) : GaugeEquivalent F x x := by
  change x - x ∈ LinearMap.range F
  simpa using (LinearMap.range F).zero_mem

/-- Gauge equivalence is symmetric. -/
theorem symm (F : Module.End R M) {x y : M}
    (h : GaugeEquivalent F x y) : GaugeEquivalent F y x := by
  rcases h with ⟨g, hg⟩
  refine ⟨-g, ?_⟩
  rw [map_neg, hg]
  module

/-- Gauge equivalence is transitive. -/
theorem trans (F : Module.End R M) {x y z : M}
    (hxy : GaugeEquivalent F x y) (hyz : GaugeEquivalent F y z) :
    GaugeEquivalent F x z := by
  rcases hxy with ⟨a, ha⟩
  rcases hyz with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [map_add, ha, hb]
  module

/-- The cleaning relation is an equivalence relation. -/
theorem equivalence (F : Module.End R M) :
    Equivalence (GaugeEquivalent F) :=
  ⟨refl F, fun _ _ => symm F, fun _ _ _ => trans F⟩

/-- Adding a gauge image does not change the presentation class. -/
theorem add_image (F : Module.End R M) (x g : M) :
    GaugeEquivalent F (x + F g) x := by
  refine ⟨g, ?_⟩
  module

/-- Subtracting a gauge image does not change the presentation class. -/
theorem sub_image (F : Module.End R M) (x g : M) :
    GaugeEquivalent F (x - F g) x := by
  refine ⟨-g, ?_⟩
  rw [map_neg]
  module

/-- An operator preserves gauge equivalence when it commutes with the gauge
operator. -/
theorem map_preserves
    (F D : Module.End R M)
    (hcomm : D.comp F = F.comp D)
    {x y : M} (hxy : GaugeEquivalent F x y) :
    GaugeEquivalent F (D x) (D y) := by
  rcases hxy with ⟨g, hg⟩
  refine ⟨D g, ?_⟩
  have hpoint := congrArg (fun T : Module.End R M => T g) hcomm
  change D (F g) = F (D g) at hpoint
  rw [← hpoint, ← map_sub, hg]

/-- A family of operators is compatible with cleaning when every member
commutes with the gauge operator. -/
def FamilyCompatible (F : Module.End R M)
    (ops : ι → Module.End R M) : Prop :=
  ∀ i, (ops i).comp F = F.comp (ops i)

/-- Every compatible operator in the family preserves gauge equivalence. -/
theorem family_map_preserves
    (F : Module.End R M) (ops : ι → Module.End R M)
    (hcompat : FamilyCompatible F ops)
    (i : ι) {x y : M} (hxy : GaugeEquivalent F x y) :
    GaugeEquivalent F (ops i x) (ops i y) :=
  map_preserves F (ops i) (hcompat i) hxy

/-- Apply a finite word of operators. -/
def applyWord (ops : ι → Module.End R M) : List ι → M → M
  | [], x => x
  | i :: word, x => ops i (applyWord ops word x)

/-- Every finite compatible operator word preserves cleaning equivalence. -/
theorem applyWord_preserves
    (F : Module.End R M) (ops : ι → Module.End R M)
    (hcompat : FamilyCompatible F ops)
    (word : List ι) {x y : M} (hxy : GaugeEquivalent F x y) :
    GaugeEquivalent F (applyWord ops word x) (applyWord ops word y) := by
  induction word with
  | nil => exact hxy
  | cons i word ih =>
      exact family_map_preserves F ops hcompat i (ih hxy)

end

end FrobeniusGaugeRelation
end PCRLean
