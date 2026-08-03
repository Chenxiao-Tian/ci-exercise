import Mathlib
import PCRLean.ActualIdealGluing

/-!
# Invertible-matrix gauge invariance of centre generators

Local equations of a regular immersion need not agree componentwise on an
overlap.  They may differ by a `GL_r` change of conormal frame.  If `f` is a
finite equation vector and `M` is an invertible matrix, then the transformed
vector

`g = M.mulVec f`

generates exactly the same ideal as `f`.

This is the correct higher-rank replacement for unit changes of a principal
exceptional equation.  It upgrades overlap descent from equality-valued Čech
data to gauge-valued data and allows nontrivial conormal bundles.

The module proves ideal invariance from explicit left and right inverse matrix
identities.  A scheme-level application must construct these matrices on every
overlap and verify their cocycle law.
-/

namespace PCRLean
namespace Experimental
namespace InvertibleMatrixGeneratorGauge

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- A finite gauge matrix with an explicit two-sided inverse. -/
structure Gauge where
  matrix : Matrix ι ι R
  inverse : Matrix ι ι R
  inverse_mul : inverse * matrix = 1
  mul_inverse : matrix * inverse = 1

namespace Gauge

variable (G : Gauge (R := R) (ι := ι))

/-- Gauge transform of a finite generator vector. -/
def transform (f : ι → R) : ι → R :=
  G.matrix.mulVec f

/-- The inverse gauge recovers the original vector. -/
theorem inverse_transform (f : ι → R) :
    G.inverse.mulVec (G.transform f) = f := by
  rw [transform, ← Matrix.mulVec_mulVec, G.inverse_mul]
  simp

/-- Transforming by the inverse and then by the gauge also recovers the input. -/
theorem transform_inverse (g : ι → R) :
    G.matrix.mulVec (G.inverse.mulVec g) = g := by
  rw [← Matrix.mulVec_mulVec, G.mul_inverse]
  simp

/-- Every transformed generator is a finite linear combination of the original
frame. -/
theorem transformed_combination (f : ι → R) (i : ι) :
    G.transform f i = ∑ j, G.matrix i j * f j := by
  rfl

/-- Every original generator is a finite linear combination of the transformed
frame. -/
theorem original_combination (f : ι → R) (i : ι) :
    f i = ∑ j, G.inverse i j * G.transform f j := by
  have h := congrFun (G.inverse_transform f) i
  simpa [Matrix.mulVec, dotProduct] using h.symm

/-- Main gauge-invariance theorem for the actual generated ideal. -/
theorem generatedIdeal_transform_eq (f : ι → R) :
    ActualIdealGluing.generatedIdeal (G.transform f) =
      ActualIdealGluing.generatedIdeal f := by
  exact ActualIdealGluing.generatedIdeal_eq_of_mutual_combinations
    (G.transform f) f G.matrix G.inverse
    (G.transformed_combination f)
    (G.original_combination f)

/-- Package the gauge change as a generator-frame equivalence. -/
def frameEquivalence (f : ι → R) :
    ActualIdealGluing.GeneratorFrameEquivalence (G.transform f) f where
  forward := G.matrix
  backward := G.inverse
  reconstruct_g := G.transformed_combination f
  reconstruct_h := G.original_combination f

end Gauge

/-- A chart-indexed gauge atlas of local generator frames. -/
structure Atlas (Chart : Type*) [Fintype Chart] where
  generator : Chart → ι → R
  gauge : ∀ c d : Chart, Gauge (R := R) (ι := ι)
  transition : ∀ c d,
    (gauge c d).transform (generator d) = generator c

namespace Atlas

variable {Chart : Type*} [Fintype Chart]
    (A : Atlas (R := R) (ι := ι) Chart)

/-- Gauge-related chart frames generate the same ideal. -/
theorem ideal_eq (c d : Chart) :
    ActualIdealGluing.generatedIdeal (A.generator c) =
      ActualIdealGluing.generatedIdeal (A.generator d) := by
  rw [← A.transition c d]
  exact (A.gauge c d).generatedIdeal_transform_eq (A.generator d)

end Atlas

end

end InvertibleMatrixGeneratorGauge
end Experimental
end PCRLean
