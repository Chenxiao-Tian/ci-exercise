import PCRLean.GenerationalRank
import PCRLean.OddCusp
import PCRLean.QuadraticDebt
import PCRLean.NoRecharge
import PCRLean.PolynomialCharts
import PCRLean.FrobeniusPacket
import PCRLean.EulerRadicial
import PCRLean.RadicialJacobian
import PCRLean.QuasilinearSplit
import PCRLean.CechEffectivity
import PCRLean.CartierFiniteMemory
import PCRLean.NoetherianTraceMemory
import PCRLean.DifferentialOrbitKernel
import PCRLean.SourcePartition
import PCRLean.MarkedIdeal
import PCRLean.CentrePermissibility
import PCRLean.OwnerJoint
import PCRLean.OddCuspAffine
import PCRLean.TameQuadraticAffine
import PCRLean.ASQAffine
import PCRLean.ReesFoundation
import PCRLean.ResolutionCompiler
import PCRLean.ChamberPrograms
import PCRLean.ConditionalMaster

namespace PCRLean

/-- Machine-readable summary of the kernel-certified component layer.
This theorem intentionally states only what the imported Lean proofs establish. -/
theorem certified_component_summary :
    WellFounded GenRank.Lt ∧
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
