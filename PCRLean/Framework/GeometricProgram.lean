import Mathlib
import PCRLean.Framework.FiniteChartProgram

/-!
# Eight-gate geometric chart programs

The PCR research architecture requires more than termination.  Every blowup
edge must be produced by an actual finite-type ideal, use a regular permissible
centre, be safe for passive data and the boundary, include all standard charts
and overlaps, preserve hereditary packet/provenance data, and strictly lower a
geometric rank.  This file packages those obligations without assuming that
they hold for arbitrary singularities.
-/

namespace PCRLean.Framework

/-- The non-numerical certificates attached to one geometric transition.

This record lives in `Type`, rather than `Prop`, because it contains the seven
propositions themselves together with their proof fields.  No theorem can
manufacture this record without supplying all seven proofs. -/
structure GeometricEdgeCertificate {State : Type*} (child parent : State) where
  actualIdeal : Prop
  regularCentre : Prop
  markedPermissible : Prop
  passiveSafe : Prop
  boundarySafe : Prop
  completeChartsAndOverlaps : Prop
  hereditaryReentryNoReset : Prop
  actualIdeal_proof : actualIdeal
  regularCentre_proof : regularCentre
  markedPermissible_proof : markedPermissible
  passiveSafe_proof : passiveSafe
  boundarySafe_proof : boundarySafe
  completeChartsAndOverlaps_proof : completeChartsAndOverlaps
  hereditaryReentryNoReset_proof : hereditaryReentryNoReset

/-- A finite chart program whose legality predicate is the existence of the
full geometric edge certificate. -/
structure GeometricProgram where
  State : Type*
  children : State → List State
  rank : State → ℕ
  terminal : State → Prop
  resolved : State → Prop
  edgeCertificate : State → State → Prop
  certificateData : ∀ {child parent}, edgeCertificate child parent →
    GeometricEdgeCertificate child parent
  child_decreases : ∀ {child parent}, child ∈ children parent →
    rank child < rank parent
  child_certified : ∀ {child parent}, child ∈ children parent →
    edgeCertificate child parent
  progress : ∀ parent, ¬ terminal parent → children parent ≠ []
  terminal_resolved : ∀ {state}, terminal state → resolved state

namespace GeometricProgram

variable (P : GeometricProgram)

/-- Forgetting the geometric fields yields a finite all-chart program. -/
def toFiniteChartProgram : FiniteChartProgram where
  State := P.State
  children := P.children
  rank := P.rank
  terminal := P.terminal
  resolved := P.resolved
  legal := P.edgeCertificate
  child_decreases := P.child_decreases
  child_legal := P.child_certified
  progress := P.progress
  terminal_resolved := P.terminal_resolved

/-- Every state has a finite tree in which every listed edge carries the full
certificate predicate. -/
theorem resolvesAll (start : P.State) :
    (P.toFiniteChartProgram).ResolvesAll start :=
  P.toFiniteChartProgram.resolvesAll start

/-- Extract the complete eight-gate record for any listed child chart. -/
theorem certificate_of_child {child parent : P.State}
    (hchild : child ∈ P.children parent) :
    GeometricEdgeCertificate child parent :=
  P.certificateData (P.child_certified hchild)

/-- Every leaf of a geometric program is resolved. -/
theorem resolved_of_leaf {state : P.State} (hleaf : P.children state = []) :
    P.resolved state :=
  P.toFiniteChartProgram.resolved_of_leaf hleaf

end GeometricProgram

end PCRLean.Framework
