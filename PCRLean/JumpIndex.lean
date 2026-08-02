import PCRLean.NoetherianOperatorOrbit
import PCRLean.OperatorOrbitEquivFixed
import PCRLean.SplitConormalFrame
import PCRLean.ActualIdealGluing
import PCRLean.NoetherianPatchingCompiler
import PCRLean.CartierNoetherMaster

/-!
# Jump architecture index

This file is an isolated build target for the historical-jump architecture:
finite operator orbits, presentation invariance, split conormal regularity,
actual ideal gluing, and Noetherian patching.  Importing this file forces all
six components through Lean elaboration and kernel checking.
-/

namespace PCRLean.JumpIndex

#print axioms PCRLean.NoetherianOperatorOrbit.exists_finite_kernel_packet
#print axioms PCRLean.OperatorOrbitEquivFixed.map_orbitModule_eq
#print axioms PCRLean.SplitConormalFrame.Frame.isCompl_ker_range
#print axioms PCRLean.ActualIdealGluing.GeneratorFrameEquivalence.ideal_eq
#print axioms PCRLean.NoetherianPatchingCompiler.PatchedProgram.terminal_reachable
#print axioms PCRLean.CartierNoetherMaster.System.every_input_resolves

end PCRLean.JumpIndex
