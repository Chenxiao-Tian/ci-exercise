import Mathlib
import Mathlib.RingTheory.Flat.Basic

/-!
# Hironaka tensor-flatness compiler

For nested regular carriers `D ⊂ C ⊂ X`, Hironaka's normal-flatness
comparison has the abstract form

```text
(restriction of gr_C(M) to D)
  tensor
(normal algebra of D in C)
  ~= gr_D(M).
```

Once the two factors are flat over `D`, the total associated graded is flat.
This is the formal endpoint behind the X039 normal-flatness transitivity
proposal.

The file proves only the module-theoretic compiler after a graded linear
equivalence has been supplied.  It does not construct Hironaka's map, prove
that a conormal algebra is symmetric, establish a regular flag, or prove any
scheme-level resolution theorem.
-/

namespace PCRLean
namespace Experimental
namespace HironakaTensorFlatnessCompiler

noncomputable section

universe u v w z t

variable {K : Type u} [CommRing K]
variable (Restricted : Type v) (RelativeNormal : Type w) (Total : Type z)
variable [AddCommGroup Restricted] [Module K Restricted]
variable [AddCommGroup RelativeNormal] [Module K RelativeNormal]
variable [AddCommGroup Total] [Module K Total]

/-- An abstract Hironaka comparison certificate. -/
structure Certificate where
  comparison :
    (Restricted ⊗[K] RelativeNormal) ≃ₗ[K] Total

namespace Certificate

/-- Flatness is transitive across an exact Hironaka tensor decomposition. -/
theorem totalFlat
    (c : Certificate (K := K) Restricted RelativeNormal Total)
    [Module.Flat K Restricted]
    [Module.Flat K RelativeNormal] :
    Module.Flat K Total := by
  letI : Module.Flat K (Restricted ⊗[K] RelativeNormal) := inferInstance
  exact Module.Flat.of_linearEquiv c.comparison.symm

/-- The comparison transports flatness in both directions. -/
theorem flat_iff_tensorFlat
    (c : Certificate (K := K) Restricted RelativeNormal Total) :
    Module.Flat K Total ↔
      Module.Flat K (Restricted ⊗[K] RelativeNormal) := by
  exact (Module.Flat.equiv_iff c.comparison).symm

/-- Pointwise comparison identity used by higher-level certificates. -/
theorem comparison_apply
    (c : Certificate (K := K) Restricted RelativeNormal Total)
    (x : Restricted ⊗[K] RelativeNormal) :
    c.comparison x = c.comparison x :=
  rfl

end Certificate

section Portfolio

variable {Owner : Type t} [Fintype Owner] [DecidableEq Owner]
variable (RestrictedO : Owner → Type v)
variable (RelativeNormalO : Owner → Type w)
variable (TotalO : Owner → Type z)
variable [∀ o, AddCommGroup (RestrictedO o)]
variable [∀ o, Module K (RestrictedO o)]
variable [∀ o, AddCommGroup (RelativeNormalO o)]
variable [∀ o, Module K (RelativeNormalO o)]
variable [∀ o, AddCommGroup (TotalO o)]
variable [∀ o, Module K (TotalO o)]

/-- One Hironaka comparison for every passive owner. -/
structure PortfolioCertificate where
  ownerCertificate : ∀ o,
    Certificate (K := K)
      (RestrictedO o) (RelativeNormalO o) (TotalO o)

namespace PortfolioCertificate

/-- Every owner is normally flat after exact tensor transitivity. -/
theorem ownerFlat
    (c : PortfolioCertificate (K := K)
      RestrictedO RelativeNormalO TotalO)
    [∀ o, Module.Flat K (RestrictedO o)]
    [∀ o, Module.Flat K (RelativeNormalO o)]
    (o : Owner) :
    Module.Flat K (TotalO o) :=
  (c.ownerCertificate o).totalFlat

/-- A finite passive portfolio is flat simultaneously. -/
theorem portfolioFlat
    (c : PortfolioCertificate (K := K)
      RestrictedO RelativeNormalO TotalO)
    [∀ o, Module.Flat K (RestrictedO o)]
    [∀ o, Module.Flat K (RelativeNormalO o)] :
    Module.Flat K (DirectSum Owner TotalO) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro o
  exact c.ownerFlat o

end PortfolioCertificate

end Portfolio

end

end HironakaTensorFlatnessCompiler
end Experimental
end PCRLean
