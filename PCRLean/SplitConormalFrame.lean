import Mathlib

/-!
# Split conormal frames and regular linear kernels

A finite packet of conormal functionals defines a split linear centre once its
evaluation map has an explicit linear right inverse. The splitting is a
concrete direct-summand certificate: the ambient module decomposes as the common
kernel of the packet plus a transverse free summand.

All statements in this file hold over an arbitrary commutative ring; no field
or division hypothesis is used. The public scalar parameter remains named `K`
for compatibility with the established formalization API.
-/

namespace PCRLean
namespace SplitConormalFrame

noncomputable section

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w}
variable [CommRing K] [AddCommGroup V] [Module K V]

/-- A conormal evaluation map with an explicit right inverse. -/
structure Frame where
  eval : V →ₗ[K] (ι → K)
  split : (ι → K) →ₗ[K] V
  rightInverse : eval.comp split = LinearMap.id

namespace Frame

variable (F : Frame (K := K) (V := V) (ι := ι))

/-- Pointwise form of the right-inverse identity. -/
theorem eval_split (a : ι → K) : F.eval (F.split a) = a := by
  have h := congrArg
    (fun L : (ι → K) →ₗ[K] (ι → K) => L a) F.rightInverse
  simpa using h

/-- A split conormal evaluation is surjective. -/
theorem eval_surjective : Function.Surjective F.eval := by
  intro a
  exact ⟨F.split a, F.eval_split a⟩

/-- The transverse splitting is injective. -/
theorem split_injective : Function.Injective F.split := by
  intro a b hab
  have h := congrArg F.eval hab
  simpa [F.eval_split] using h

/-- Projection of an ambient vector onto the persistent kernel. -/
def kernelPart (x : V) : V := x - F.split (F.eval x)

/-- The projected vector lies in the common kernel. -/
theorem kernelPart_mem (x : V) : F.kernelPart x ∈ LinearMap.ker F.eval := by
  change F.eval (x - F.split (F.eval x)) = 0
  rw [map_sub, F.eval_split, sub_self]

/-- The transverse component lies in the range of the splitting. -/
theorem transversePart_mem (x : V) :
    F.split (F.eval x) ∈ LinearMap.range F.split := by
  exact ⟨F.eval x, rfl⟩

/-- Every ambient vector is the sum of a kernel vector and a transverse vector. -/
theorem kernel_add_transverse (x : V) :
    F.kernelPart x + F.split (F.eval x) = x := by
  simp [kernelPart]

/-- The persistent kernel and transverse range span the whole ambient module. -/
theorem ker_sup_range_eq_top :
    LinearMap.ker F.eval ⊔ LinearMap.range F.split = ⊤ := by
  apply top_unique
  intro x hx
  have hk : F.kernelPart x ∈
      LinearMap.ker F.eval ⊔ LinearMap.range F.split :=
    (show LinearMap.ker F.eval ≤
      LinearMap.ker F.eval ⊔ LinearMap.range F.split from le_sup_left)
      (F.kernelPart_mem x)
  have ht : F.split (F.eval x) ∈
      LinearMap.ker F.eval ⊔ LinearMap.range F.split :=
    (show LinearMap.range F.split ≤
      LinearMap.ker F.eval ⊔ LinearMap.range F.split from le_sup_right)
      (F.transversePart_mem x)
  have hs := (LinearMap.ker F.eval ⊔ LinearMap.range F.split).add_mem hk ht
  rw [F.kernel_add_transverse x] at hs
  exact hs

/-- The persistent kernel meets the transverse range only in zero. -/
theorem ker_disjoint_range :
    Disjoint (LinearMap.ker F.eval) (LinearMap.range F.split) := by
  rw [Submodule.disjoint_def]
  intro x hxker hxrange
  rcases hxrange with ⟨a, rfl⟩
  have hzero : a = 0 := by
    have heval : F.eval (F.split a) = 0 := hxker
    simpa [F.eval_split] using heval
  simp [hzero]

/-- The two certified submodules form an internal direct decomposition. -/
theorem isCompl_ker_range :
    IsCompl (LinearMap.ker F.eval) (LinearMap.range F.split) := by
  exact ⟨F.ker_disjoint_range,
    codisjoint_iff.mpr F.ker_sup_range_eq_top⟩

/-- A vector lies in the persistent kernel exactly when its finite conormal
coordinate packet is zero. -/
theorem mem_ker_iff (x : V) :
    x ∈ LinearMap.ker F.eval ↔ F.eval x = 0 :=
  LinearMap.mem_ker

end Frame

end

end SplitConormalFrame
end PCRLean
