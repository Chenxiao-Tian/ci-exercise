import Mathlib
import PCRLean.Chambers.FrobeniusContentProgram
import PCRLean.Chambers.OddCuspProgram
import PCRLean.Chambers.RamifiedQuadraticProgram
import PCRLean.Chambers.ArtinSchreierProgram

/-!
# The currently closed finite chamber grammar

This file combines the separately certified local programs into one finite
packet grammar.  The first three constructors end in a state labelled
`resolved`; the Artin--Schreier constructor ends in a rigorously classified
exit, because the even radicial tail is intentionally not called resolved.

The theorem is exhaustive for this inductive grammar only.  The missing
arbitrary-input enrollment theorem is not assumed or hidden.
-/

namespace PCRLean.Chambers.ClosedGrammar

namespace F := PCRLean.Chambers.FrobeniusContentProgram
namespace O := PCRLean.Chambers.OddCuspProgram
namespace R := PCRLean.Chambers.RamifiedQuadraticProgram
namespace A := PCRLean.Chambers.ArtinSchreierProgram

/-- Packet families whose current certified programs end in resolved leaves. -/
inductive ResolvedPacket where
  | frobeniusContent (depth : ℕ)
  | oddCusp (depth : ℕ)
  | ramifiedQuadratic (depth : ℕ)
  deriving DecidableEq, Repr

/-- The exact path-to-resolution proposition for each closed packet family. -/
def Resolves : ResolvedPacket → Prop
  | .frobeniusContent depth =>
      ∃ finish,
        Relation.ReflTransGen F.step finish (F.State.active depth) ∧
        F.resolved finish
  | .oddCusp depth =>
      ∃ finish,
        Relation.ReflTransGen O.step finish (O.State.active depth) ∧
        O.resolved finish
  | .ramifiedQuadratic depth =>
      ∃ finish,
        Relation.ReflTransGen R.step finish (R.State.active depth) ∧
        R.resolved finish

/-- Every packet in the current resolved grammar has a kernel-checked finite
path to a resolved state. -/
theorem resolves_every_packet (p : ResolvedPacket) : Resolves p := by
  cases p with
  | frobeniusContent depth =>
      exact F.program.reaches_resolved (F.State.active depth)
  | oddCusp depth =>
      exact O.program.reaches_resolved (O.State.active depth)
  | ramifiedQuadratic depth =>
      exact R.program.reaches_resolved (R.State.active depth)

/-- The wider grammar includes the characteristic-two Artin--Schreier family,
whose certified program reaches a classified exit rather than claiming that
every exit is already resolved. -/
inductive ClassifiedPacket where
  | resolved (packet : ResolvedPacket)
  | artinSchreier (m r : ℕ)
  deriving DecidableEq, Repr

/-- Exact certified outcome for the wider grammar. -/
def HasCertifiedOutcome : ClassifiedPacket → Prop
  | .resolved packet => Resolves packet
  | .artinSchreier m r =>
      ∃ finish,
        Relation.ReflTransGen A.step finish (A.State.active m r) ∧
        A.terminal finish

/-- Every packet in the current wider grammar reaches its certified outcome. -/
theorem classifies_every_packet (p : ClassifiedPacket) :
    HasCertifiedOutcome p := by
  cases p with
  | resolved packet => exact resolves_every_packet packet
  | artinSchreier m r => exact A.program.reaches_terminal (A.State.active m r)

end PCRLean.Chambers.ClosedGrammar
