import PCRLean.Chambers.FrobeniusContent
import PCRLean.Chambers.OddCusp
import PCRLean.Chambers.RamifiedQuadratic
import PCRLean.Chambers.ArtinSchreier
import PCRLean.Termination.Generational
import PCRLean.Framework.RankedSystem
import PCRLean.NoGo.PersistentObstruction

/-!
# Certified kernel index

Only declarations proved without `sorry`, `admit`, or project-specific axioms
are imported here.  This is deliberately not a theorem of arbitrary-dimensional
resolution.  It is the current kernel-checked local algebra, termination core,
and obstruction-audit layer.
-/

namespace PCRLean.Certified

open PCRLean.Chambers
open PCRLean.Termination

/-- The restricted generational compiler has a genuine well-founded backend. -/
theorem generational_backend_wf :
    WellFounded Generational.GenLt :=
  Generational.genLt_wellFounded

end PCRLean.Certified

#print axioms PCRLean.Chambers.FrobeniusContent.active_factorization
#print axioms PCRLean.Chambers.FrobeniusContent.sibling_factorization
#print axioms PCRLean.Chambers.OddCusp.sChart_factorization
#print axioms PCRLean.Chambers.OddCusp.yChart_factorization
#print axioms PCRLean.Chambers.RamifiedQuadratic.collision_factorization
#print axioms PCRLean.Chambers.RamifiedQuadratic.sibling_factorization
#print axioms PCRLean.Chambers.ArtinSchreier.collision_factorization
#print axioms PCRLean.Chambers.ArtinSchreier.sibling_factorization
#print axioms PCRLean.Termination.Generational.genLt_wellFounded
#print axioms PCRLean.Framework.RankedSystem.step_wellFounded
#print axioms PCRLean.Framework.CertifiedProgram.reaches_terminal
#print axioms PCRLean.Framework.CertifiedProgram.reaches_resolved
#print axioms PCRLean.NoGo.ObstructionSystem.preserves_path
#print axioms PCRLean.NoGo.ObstructionSystem.nonzero_persists
#print axioms PCRLean.Certified.generational_backend_wf
