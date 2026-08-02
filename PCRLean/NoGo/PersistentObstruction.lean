import Mathlib

/-!
# Persistent-obstruction no-go

A centre program cannot clear an obstruction that is invariant under every
allowed transition.  This elementary theorem is the formal backend of several
geometric no-go tests, including the warning that identity blowups cannot kill
a nontrivial root-torsor class.
-/

namespace PCRLean.NoGo

/-- A transition system equipped with an exactly preserved obstruction. -/
structure ObstructionSystem where
  State : Type*
  Obstruction : Type*
  step : State → State → Prop
  obstruction : State → Obstruction
  step_preserves : ∀ {child parent}, step child parent →
    obstruction child = obstruction parent

namespace ObstructionSystem

variable (S : ObstructionSystem)

/-- The obstruction is preserved along every finite certified path. -/
theorem preserves_path {finish start : S.State}
    (h : Relation.ReflTransGen S.step finish start) :
    S.obstruction finish = S.obstruction start := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (S.step_preserves hstep)

/-- If the initial obstruction is nonzero, no finite path of obstruction-
preserving moves reaches a zero-obstruction state. -/
theorem nonzero_persists [Zero S.Obstruction]
    {finish start : S.State} (hstart : S.obstruction start ≠ 0)
    (h : Relation.ReflTransGen S.step finish start) :
    S.obstruction finish ≠ 0 := by
  intro hfinish
  apply hstart
  calc
    S.obstruction start = S.obstruction finish := (S.preserves_path h).symm
    _ = 0 := hfinish

end ObstructionSystem

end PCRLean.NoGo
