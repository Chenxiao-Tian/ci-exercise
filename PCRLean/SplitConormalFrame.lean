import Mathlib

/-!
# Split conormal frames and regular linear kernels

A finite packet of conormal functionals defines a regular linear centre once
its evaluation map has an explicit linear section.  The section is a concrete
regularity certificate: the ambient tangent module decomposes as the common
kernel of the packet plus a transverse free summand.

The geometric realization problem is to construct such a split frame from the
intrinsic Hasse--Cartier packet on a neighbourhood of the proposed centre.
-/

namespace PCRLean
namespace SplitConormalFrame

noncomputable section

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A conormal evaluation map with an explicit right inverse. -/
structure Frame where
  eval : V →ₗ[K] (ι → K)
  section : (ι → K) →ₗ[K] V
  rightInverse : eval.comp section = LinearMap.id

namespace Frame

variable (F : Frame (K := K) (V := V) (ι := ι))

/-- Pointwise form of the right-inverse identity. -/
theorem eval_section (a : ι → K) : F.eval (F.section a) = a := by
  have h := congrArg
    (fun L : (ι → K) →ₗ[K] (ι → K) => L a) F.rightInverse
  simpa using h

/-- A split conormal evaluation is surjective. -/
theorem eval_surjective : Function.Surjective F.eval := by
  intro a
  exact ⟨F.section a, F.eval_section a⟩

/-- The transverse section is injective. -/
theorem section_injective : Function.Injective F.section := by
  intro a b hab
  have h := congrArg F.eval hab
  simpa [F.eval_section] using h

/-- Projection of an ambient vector onto the persistent kernel. -/
def kernelPart (x : V) : V := x - F.section (F.eval x)

/-- The projected vector lies in the common kernel. -/
theorem kernelPart_mem (x : V) : F.kernelPart x ∈ LinearMap.ker F.eval := by
  change F.eval (x - F.section (F.eval x)) = 0
  rw [map_sub, F.eval_section, sub_self]

/-- The transverse component lies in the range of the section. -/
theorem transversePart_mem (x : V) :
    F.section (F.eval x) ∈ LinearMap.range F.section := by
  exact ⟨F.eval x, rfl⟩

/-- Every ambient vector is the sum of a kernel vector and a transverse vector. -/
theorem kernel_add_transverse (x : V) :
    F.kernelPart x + F.section (F.eval x) = x := by
  simp [kernelPart]

/-- The persistent kernel and transverse range span the whole ambient module. -/
theorem ker_sup_range_eq_top :
    LinearMap.ker F.eval ⊔ LinearMap.range F.section = ⊤ := by
  apply top_unique
  intro x hx
  have hk : F.kernelPart x ∈
      LinearMap.ker F.eval ⊔ LinearMap.range F.section :=
    le_sup_left (F.kernelPart_mem x)
  have ht : F.section (F.eval x) ∈
      LinearMap.ker F.eval ⊔ LinearMap.range F.section :=
    le_sup_right (F.transversePart_mem x)
  have hs := (LinearMap.ker F.eval ⊔ LinearMap.range F.section).add_mem hk ht
  simpa [F.kernel_add_transverse x] using hs

/-- The persistent kernel meets the transverse range only in zero. -/
theorem ker_disjoint_range :
    Disjoint (LinearMap.ker F.eval) (LinearMap.range F.section) := by
  rw [Submodule.disjoint_def]
  intro x hxker hxrange
  rcases hxrange with ⟨a, rfl⟩
  have hzero : a = 0 := by
    have heval : F.eval (F.section a) = 0 := hxker
    simpa [F.eval_section] using heval
  simp [hzero]

/-- The two certified submodules form an internal direct decomposition. -/
theorem isCompl_ker_range :
    IsCompl (LinearMap.ker F.eval) (LinearMap.range F.section) := by
  exact ⟨F.ker_disjoint_range, F.ker_sup_range_eq_top⟩

/-- A vector lies in the persistent kernel exactly when its finite conormal
coordinate packet is zero. -/
theorem mem_ker_iff (x : V) :
    x ∈ LinearMap.ker F.eval ↔ F.eval x = 0 :=
  LinearMap.mem_ker

end Frame

end

end SplitConormalFrame
end PCRLean
