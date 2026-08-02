import Mathlib
import PCRLean.Framework.GeometricProgram

/-!
# Universal resolution compiler

A universal resolution theorem is obtained once every admissible input is
assigned a finite geometric chart program together with an initial state.  The
compiler below contains no hidden geometry: all actual-centre, legality,
all-chart, reentry, and strict-descent obligations reside in the supplied
`GeometricProgram`.
-/

namespace PCRLean.Framework

/-- A family of completely certified geometric programs, one for each input. -/
structure UniversalProgramFamily where
  Input : Type*
  program : Input → GeometricProgram
  initial : ∀ input, (program input).State

namespace UniversalProgramFamily

variable (F : UniversalProgramFamily)

/-- Every input in a universally certified family has a complete finite
all-chart resolution tree. -/
theorem resolvesAllInputs (input : F.Input) :
    ((F.program input).toFiniteChartProgram).ResolvesAll (F.initial input) :=
  (F.program input).resolvesAll (F.initial input)

/-- Every initial state that is already a leaf is resolved. -/
theorem resolvedIfInitialLeaf (input : F.Input)
    (hleaf : (F.program input).children (F.initial input) = []) :
    (F.program input).resolved (F.initial input) :=
  (F.program input).resolved_of_leaf hleaf

end UniversalProgramFamily

end PCRLean.Framework
