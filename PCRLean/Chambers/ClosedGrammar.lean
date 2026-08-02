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
        Relation.ReflTransGen
          PCRLean.Chambers.FrobeniusContentProgram.Step finish
          (PCRLean.Chambers.FrobeniusContentProgram.State.active depth) ∧
        PCRLean.Chambers.FrobeniusContentProgram.resolved finish
  | .oddCusp depth =>
      ∃ finish,
        Relation.ReflTransGen
          PCRLean.Chambers.OddCuspProgram.Step finish
          (PCRLean.Chambers.OddCuspProgram.State.active depth) ∧
        PCRLean.Chambers.OddCuspProgram.resolved finish
  | .ramifiedQuadratic depth =>
      ∃ finish,
        Relation.ReflTransGen
          PCRLean.Chambers.RamifiedQuadraticProgram.Step finish
          (PCRLean.Chambers.RamifiedQuadraticProgram.State.active depth) ∧
        PCRLean.Chambers.RamifiedQuadraticProgram.resolved finish

/-- Every packet in the current resolved grammar has a kernel-checked finite
path to a resolved state. -/
theorem resolves_every_packet (p : ResolvedPacket) : Resolves p := by
  cases p with
  | frobeniusContent depth =>
      exact PCRLean.Chambers.FrobeniusContentProgram.program.reaches_resolved
        (PCRLean.Chambers.FrobeniusContentProgram.State.active depth)
  | oddCusp depth =>
      exact PCRLean.Chambers.OddCuspProgram.program.reaches_resolved
        (PCRLean.Chambers.OddCuspProgram.State.active depth)
  | ramifiedQuadratic depth =>
      exact PCRLean.Chambers.RamifiedQuadraticProgram.program.reaches_resolved
        (PCRLean.Chambers.RamifiedQuadraticProgram.State.active depth)

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
        Relation.ReflTransGen
          PCRLean.Chambers.ArtinSchreierProgram.Step finish
          (PCRLean.Chambers.ArtinSchreierProgram.State.active m r) ∧
        PCRLean.Chambers.ArtinSchreierProgram.classifiedExit finish

/-- Every packet in the current wider grammar reaches its certified outcome. -/
theorem classifies_every_packet (p : ClassifiedPacket) :
    HasCertifiedOutcome p := by
  cases p with
  | resolved packet => exact resolves_every_packet packet
  | artinSchreier m r =>
      exact PCRLean.Chambers.ArtinSchreierProgram.program.reaches_resolved
        (PCRLean.Chambers.ArtinSchreierProgram.State.active m r)

end PCRLean.Chambers.ClosedGrammar
