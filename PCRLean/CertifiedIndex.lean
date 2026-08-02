import PCRLean.GenerationalRank
import PCRLean.OddCusp
import PCRLean.QuadraticDebt
import PCRLean.NoRecharge

namespace PCRLean

/-- Machine-readable summary of the kernel-certified component layer.
This theorem intentionally states only what the imported Lean proofs establish. -/
theorem certified_component_summary :
    GenRank.wellFounded GenRank.Lt ∧
    (∀ N : Nat, 0 < OddCusp.certifiedWordLength N) ∧
    (∀ B : Nat, ∃ N, B < QuadraticDebt.collisionDebt N) ∧
    Function.Injective NoRecharge.freshBirthIdentity := by
  constructor
  · exact GenRank.wellFounded
  constructor
  · exact OddCusp.certifiedWordLength_pos
  constructor
  · exact QuadraticDebt.noFixedDirectionDepthBound
  · exact NoRecharge.freshBirthIdentity_injective

end PCRLean
