import Std.Tactic

namespace PCRLean
namespace QuadraticDebt

/-- Collision debt of the ramified quadratic order `z^2 = u t^N`. -/
def collisionDebt (N : Nat) : Nat := N / 2

/-- One collision-cylinder blowup changes `N` to `N-2` and pays exactly
one layer of collision debt. -/
theorem collisionDebt_recurrence {N : Nat} (hN : 2 ≤ N) :
    collisionDebt (N - 2) + 1 = collisionDebt N := by
  unfold collisionDebt
  omega

/-- The collision exponent itself strictly decreases on the active chart. -/
theorem exponentDrops {N : Nat} (hN : 2 ≤ N) : N - 2 < N := by
  omega

/-- The tame collision phase has finite height `floor(N/2)`. -/
theorem collisionPhaseFinite (N : Nat) : collisionDebt N ≤ N := by
  unfold collisionDebt
  omega

/-- The direction support alone cannot bound the collision depth: for every
finite proposed bound there is a packet with larger debt. -/
theorem noFixedDirectionDepthBound (B : Nat) :
    ∃ N, B < collisionDebt N := by
  refine ⟨2 * (B + 1), ?_⟩
  unfold collisionDebt
  omega

/-- Artin--Schreier collision parameters. -/
structure ASQState where
  linearDepth : Nat
  tailOrder : Nat
  deriving Repr, DecidableEq

/-- The unique collision-active chart update `(m,r) -> (m-1,r-2)`. -/
def ASQState.next (s : ASQState) : ASQState :=
  ⟨s.linearDepth - 1, s.tailOrder - 2⟩

/-- A simple finite measure for the explicit ASQ collision phase. -/
def ASQState.measure (s : ASQState) : Nat := s.linearDepth + s.tailOrder

/-- Under the collision hypotheses both ASQ parameters fall, hence their sum
falls strictly. -/
theorem ASQState.measureDrops (s : ASQState)
    (hm : 1 ≤ s.linearDepth) (hr : 2 ≤ s.tailOrder) :
    s.next.measure < s.measure := by
  simp [ASQState.next, ASQState.measure]
  omega

/-- The regularization depth used by the explicit characteristic-two order. -/
def asqDebt (m r : Nat) : Nat := min m (r / 2)

/-- The ASQ debt never exceeds either visible bound. -/
theorem asqDebt_le_left (m r : Nat) : asqDebt m r ≤ m := by
  exact min_le_left _ _

/-- The ASQ debt never exceeds half the tail order. -/
theorem asqDebt_le_right (m r : Nat) : asqDebt m r ≤ r / 2 := by
  exact min_le_right _ _

end QuadraticDebt
end PCRLean
