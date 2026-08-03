import Mathlib
import PCRLean.Experimental.FittingMinorAtlas
import PCRLean.Experimental.FittingGraphCentreAtlas
import PCRLean.Experimental.DetUnitLinearSystemGraph

/-!
# Fitting atlases of determinant-unit linear systems

A finite Fitting atlas provides determinants `d_c` whose basic opens cover the
base. On the chart `R_{d_c}`, suppose a square affine linear system has
coefficient matrix `M_c` and

`det(M_c) = image(d_c)`.

The distinguished determinant is a unit on the chart, so the matrix is
canonically invertible. The system therefore produces a graph tuple

`h_c = M_c⁻¹ b_c`

and the system-equation ideal is exactly the graph ideal.

This module removes the local graph tuple from the input of the Fitting graph
atlas. The remaining compatibility problem is to prove that systems obtained
from the same core agree after double localization; the next overlap compiler
derives compatibility of the solutions automatically.
-/

namespace PCRLean
namespace Experimental
namespace FittingLinearSystemAtlas

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open FittingGraphCentreAtlas

variable (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))

/-- A determinant-normalized affine linear system on every Fitting chart. -/
structure Data where
  matrix : ∀ c : Chart, Matrix ι ι (ChartRing A c)
  rhs : ∀ c : Chart, ι → ChartRing A c
  det_eq : ∀ c : Chart,
    (matrix c).det =
      algebraMap R (ChartRing A c) (A.determinant c)

namespace Data

variable (D : Data (ι := ι) A)

/-- Every chart matrix has unit determinant. -/
theorem det_isUnit (c : Chart) : IsUnit (D.matrix c).det := by
  rw [D.det_eq c]
  exact A.determinant_isUnit_away c

/-- Canonical determinant-unit system on one chart. -/
noncomputable def localSystem (c : Chart) :
    DetUnitLinearSystemGraph.System
      (R := ChartRing A c) (ι := ι) where
  matrix := D.matrix c
  rhs := D.rhs c
  det_isUnit := D.det_isUnit c

/-- Canonical graph solution on one chart. -/
noncomputable def graph (c : Chart) : ι → ChartRing A c :=
  (D.localSystem c).solution

/-- The graph tuple solves the local affine linear system. -/
theorem matrix_mulVec_graph (c : Chart) :
    (D.matrix c).mulVec (D.graph c) = D.rhs c := by
  simpa [graph, localSystem] using
    (D.localSystem c).matrix_mulVec_solution

/-- Pointwise local system equation. -/
theorem matrix_mulVec_graph_apply (c : Chart) (i : ι) :
    (D.matrix c).mulVec (D.graph c) i = D.rhs c i := by
  rw [D.matrix_mulVec_graph]

/-- The local system equations generate exactly the local graph ideal. -/
theorem equationIdeal_eq_graphIdeal (c : Chart) :
    (D.localSystem c).equationIdeal =
      PolynomialGraphCentreHeredity.graphIdeal (D.graph c) :=
  (D.localSystem c).equationIdeal_eq_graphIdeal

/-- Derived graph-atlas data. -/
noncomputable def toGraphAtlasData :
    GraphAtlasData (ι := ι) A where
  graph := D.graph

/-- Every chart receives the actual regular graph-centre certificate. -/
noncomputable def localCentreCertificate
    (p : Nat) [Fact p.Prime] [CharP R p]
    (c : Chart) (e : Nat) :
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p (D.graph c) e :=
  (D.toGraphAtlasData.localCentreCertificate p c e)

/-- Finite determinant cover plus all local system/graph certificates. -/
structure Certificate (p : Nat) [Fact p.Prime] [CharP R p]
    (e : Nat) where
  cover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤
  determinantUnit : ∀ c : Chart, IsUnit (D.matrix c).det
  equationSolved : ∀ c : Chart,
    (D.matrix c).mulVec (D.graph c) = D.rhs c
  equationEqualsGraph : ∀ c : Chart,
    (D.localSystem c).equationIdeal =
      PolynomialGraphCentreHeredity.graphIdeal (D.graph c)
  localCentre : ∀ c : Chart,
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p (D.graph c) e

/-- Assemble the finite local-system atlas certificate. -/
noncomputable def certificate
    (p : Nat) [Fact p.Prime] [CharP R p]
    (e : Nat) : Certificate A D p e where
  cover := A.basicOpen_cover
  determinantUnit := D.det_isUnit
  equationSolved := D.matrix_mulVec_graph
  equationEqualsGraph := D.equationIdeal_eq_graphIdeal
  localCentre := D.localCentreCertificate p

end Data

end

end FittingLinearSystemAtlas
end Experimental
end PCRLean
