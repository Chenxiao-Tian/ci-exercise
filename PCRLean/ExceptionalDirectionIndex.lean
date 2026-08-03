import PCRLean.ExceptionalDirectionCompiler

namespace PCRLean.ExceptionalDirectionIndex

variable {Primary : Type*}
variable (primaryLt : Primary → Primary → Prop)
variable (primaryWf : WellFounded primaryLt)

#print axioms PCRLean.ExceptionalDirectionCompiler.rankLt_wellFounded
#print axioms PCRLean.ExceptionalDirectionCompiler.rankStep_wellFounded
#print axioms PCRLean.ExceptionalDirectionCompiler.Program.terminal_reachable
#print axioms PCRLean.ExceptionalDirectionCompiler.Program.no_infinite_execution

end PCRLean.ExceptionalDirectionIndex
