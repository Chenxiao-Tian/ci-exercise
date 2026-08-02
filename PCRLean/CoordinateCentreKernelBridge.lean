import Mathlib
import PCRLean.CoordinateBlowupChart
import PCRLean.CoordinateKernelIdeal

/-!
# A coordinate-kernel model for a regular centre

The passive-coordinate inclusion `α → α ⊕ ι` has a canonical retraction which
kills every complementary coordinate.  Its kernel is an actual proper ideal,
and the quotient is the passive polynomial ring.  MLEL-002 uses this module as
the regular coordinate-kernel certificate; identifying a particular intrinsic
Frobenius core with this kernel remains an explicit geometric hypothesis.
-/

namespace PCRLean
namespace CoordinateCentreKernelBridge

noncomputable section

universe u v w

variable {K : Type u} [CommRing K]
variable {α : Type v} {ι : Type w}

abbrev A := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

/-- Inclusion of passive variables into the full variable set. -/
def passiveEmbedding : α → α ⊕ ι := Sum.inl

/-- The passive inclusion is injective. -/
theorem passiveEmbedding_injective :
    Function.Injective (passiveEmbedding (α := α) (ι := ι)) := by
  intro a b h
  exact Sum.inl.inj h

/-- Actual coordinate-kernel ideal obtained by killing all complementary
variables. -/
def passiveKernel : Ideal (A (K := K) (α := α) (ι := ι)) :=
  CoordinateKernelIdeal.ideal (R := K)
    (passiveEmbedding (α := α) (ι := ι))
    (passiveEmbedding_injective (α := α) (ι := ι))

/-- Explicit quotient by the coordinate-kernel ideal. -/
noncomputable def quotientEquiv :
    (A (K := K) (α := α) (ι := ι) ⧸
        passiveKernel (K := K) (α := α) (ι := ι)) ≃+*
      MvPolynomial α K :=
  CoordinateKernelIdeal.quotientEquiv (R := K)
    (passiveEmbedding (α := α) (ι := ι))
    (passiveEmbedding_injective (α := α) (ι := ι))

/-- The coordinate-kernel ideal is proper over a nontrivial coefficient ring. -/
theorem passiveKernel_ne_top [Nontrivial K] :
    passiveKernel (K := K) (α := α) (ι := ι) ≠ ⊤ :=
  CoordinateKernelIdeal.ideal_ne_top (R := K)
    (passiveEmbedding (α := α) (ι := ι))
    (passiveEmbedding_injective (α := α) (ι := ι))

/-- Over a Noetherian coefficient ring with finitely many ambient variables,
the coordinate-kernel ideal is finitely generated. -/
theorem passiveKernel_fg
    [IsNoetherianRing K] [Finite (α ⊕ ι)] :
    (passiveKernel (K := K) (α := α) (ι := ι)).FG :=
  CoordinateKernelIdeal.ideal_fg (R := K)
    (passiveEmbedding (α := α) (ι := ι))
    (passiveEmbedding_injective (α := α) (ι := ι))

end

end CoordinateCentreKernelBridge
end PCRLean
