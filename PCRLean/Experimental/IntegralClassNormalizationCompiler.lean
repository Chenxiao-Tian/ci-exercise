import Mathlib
import PCRLean.ResolutionCompiler

/-!
# Integral-class normalization versus geometric descent

Frobenius root extraction, finite Hasse completion and cleaning are changes of
presentation inside one integral-equivalence class.  They must not be counted
as ordinary blowups and must not reset geometric history.  Conversely, a real
geometric action may change the integral class but must decrease the geometric
rank.

This file formalizes the two-level compiler.  Every accepted transition is
classified as either

* a geometric step, strictly decreasing a well-founded geometric rank; or
* a normalization step, preserving geometric rank and history exactly while
  strictly decreasing a well-founded presentation rank.

The lexicographic product is well founded.  Therefore no infinite execution can
alternate normalization and geometry to hide nontermination.  Under a progress
hypothesis every state reaches a terminal state.

The compiler does not prove that actual positive-characteristic blowups admit
this classification.  It is the backend for the missing integral-equivalence
heredity and geometric descent theorems.
-/

namespace PCRLean
namespace Experimental
namespace IntegralClassNormalizationCompiler

noncomputable section

universe u v w x

/-- A two-level geometric program with immutable history across presentation
normalization. -/
structure Program where
  State : Type u
  GeometricRank : Type v
  PresentationRank : Type w
  History : Type x
  step : State → State → Prop
  terminal : State → Prop
  geometricRank : State → GeometricRank
  presentationRank : State → PresentationRank
  history : State → History
  geometricLt : GeometricRank → GeometricRank → Prop
  presentationLt : PresentationRank → PresentationRank → Prop
  geometricWf : WellFounded geometricLt
  presentationWf : WellFounded presentationLt
  classify : ∀ {parent child}, step parent child →
    geometricLt (geometricRank child) (geometricRank parent) ∨
      (geometricRank child = geometricRank parent ∧
        presentationLt (presentationRank child) (presentationRank parent))
  normalizationHistory : ∀ {parent child}, step parent child →
    geometricRank child = geometricRank parent →
      history child = history parent
  progress : ∀ s, ¬ terminal s → ∃ t, step s t

namespace Program

variable (P : Program)

/-- Combined rank: geometry is primary, presentation complexity secondary. -/
abbrev Rank := P.GeometricRank × P.PresentationRank

/-- Lexicographic combined order. -/
def RankLt : P.Rank → P.Rank → Prop :=
  Prod.Lex P.geometricLt P.presentationLt

/-- Combined normalization/geometric rank is well founded. -/
theorem rankLt_wellFounded : WellFounded P.RankLt :=
  WellFounded.prod_lex P.geometricWf P.presentationWf

/-- Compiled rank of a state. -/
def rank (s : P.State) : P.Rank :=
  (P.geometricRank s, P.presentationRank s)

/-- Every accepted transition decreases the combined rank. -/
theorem step_decreases {parent child : P.State}
    (h : P.step parent child) :
    P.RankLt (P.rank child) (P.rank parent) := by
  rcases P.classify h with hgeom | hnormalize
  · exact Prod.Lex.left _ _ hgeom
  · exact Prod.Lex.right hnormalize.1 hnormalize.2

/-- A transition with unchanged geometric rank preserves history exactly. -/
theorem history_eq_of_geometricRank_eq
    {parent child : P.State}
    (hstep : P.step parent child)
    (hrank : P.geometricRank child = P.geometricRank parent) :
    P.history child = P.history parent :=
  P.normalizationHistory hstep hrank

/-- A transition with unchanged geometric rank strictly decreases presentation
complexity. -/
theorem presentationRank_decreases_of_geometricRank_eq
    {parent child : P.State}
    (hstep : P.step parent child)
    (hrank : P.geometricRank child = P.geometricRank parent) :
    P.presentationLt
      (P.presentationRank child) (P.presentationRank parent) := by
  rcases P.classify hstep with hgeom | hnormalize
  · have hirr : ¬ P.geometricLt
        (P.geometricRank parent) (P.geometricRank parent) :=
      P.geometricWf.asymmetric _ _
    exact False.elim (hirr (hrank ▸ hgeom))
  · exact hnormalize.2

/-- Compile into the generic termination backend. -/
def toResolutionProgram : ResolutionCompiler.Program where
  State := P.State
  Rank := P.Rank
  step := P.step
  terminal := P.terminal
  rank := P.rank
  lt := P.RankLt
  wf := P.rankLt_wellFounded
  decreases := P.step_decreases
  progress := P.progress

/-- Every state reaches a terminal descendant. -/
theorem terminal_reachable (s : P.State) :
    ∃ t, ResolutionCompiler.Reaches P.step s t ∧ P.terminal t :=
  P.toResolutionProgram.terminal_reachable s

/-- No infinite sequence can alternate normalization and geometry while
satisfying the classification. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → P.State,
      ∀ n, P.step (f n) (f (n + 1)) :=
  P.toResolutionProgram.no_infinite_execution

end Program

end

end IntegralClassNormalizationCompiler
end Experimental
end PCRLean
