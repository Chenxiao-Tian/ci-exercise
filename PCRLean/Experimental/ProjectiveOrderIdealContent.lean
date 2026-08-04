import Mathlib
import PCRLean.Experimental.ProjectiveSectionOrderIdeal

/-!
# The order ideal is the content ideal of a finite-projective section

For a module section `x`, call an ideal `I` absorbing if

`x ∈ I • P`.

A finite dual frame proves that the intrinsic order ideal is exactly the least
absorbing ideal.  This identifies the X031 order ideal with the classical
content ideal of the section.  The characterization is frame-independent even
though a frame supplies the finite reconstruction proof.
-/

namespace PCRLean
namespace Experimental
namespace ProjectiveOrderIdealContent

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal

/-- Every functional value of an `I`-multiple section lies in `I`. -/
theorem orderIdeal_le_of_section_mem_smul_top
    (x : P) (I : Ideal R)
    (hx : x ∈ I • (⊤ : Submodule R P)) :
    orderIdeal x ≤ I := by
  rw [orderIdeal, Ideal.span_le]
  rintro a ⟨f, rfl⟩
  exact Submodule.smul_induction_on hx
    (fun r hr p hp => by
      rw [f.map_smul, smul_eq_mul]
      exact I.mul_mem_right (f p) hr)
    (fun y z hy hz => by
      rw [map_add]
      exact I.add_mem hy hz)

/-- For a finite dual frame, containment of the order ideal is equivalent to
absorption of the section. -/
theorem orderIdeal_le_iff_section_mem_smul_top
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) (I : Ideal R) :
    orderIdeal x ≤ I ↔ x ∈ I • (⊤ : Submodule R P) := by
  constructor
  · intro hI
    rw [← F.reconstruct x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul
        (hI (Ideal.subset_span ⟨F.functional i, rfl⟩))
        Submodule.mem_top
  · exact orderIdeal_le_of_section_mem_smul_top x I

/-- The intrinsic order ideal is the least ideal whose scalar multiple of the
module contains the section. -/
theorem orderIdeal_isLeast_content
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) :
    IsLeast
      {I : Ideal R | x ∈ I • (⊤ : Submodule R P)}
      (orderIdeal x) := by
  constructor
  · exact ProjectiveSectionOrderIdeal.section_mem_orderIdeal_smul_top F x
  · intro I hI
    exact orderIdeal_le_of_section_mem_smul_top x I hI

end

end ProjectiveOrderIdealContent
end Experimental
end PCRLean
