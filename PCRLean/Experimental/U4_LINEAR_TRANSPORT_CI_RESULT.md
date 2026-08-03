# U4 Linear Transport CI Result

- source commit: `de5ca6dbd0163c840fe6b23db80a4c70d3b0c314`
- workflow run: `30777070488`
- placeholder rejection: success
- build: failure
- axiom audit: failure

## u4-placeholders.txt
```text
```

## u4-build.txt
```text
✔ [8475/8487] Built PCRLean.MarkedIdeal (6.7s)
⚠ [8476/8487] Built PCRLean.ActualIdealGluing (6.9s)
warning: PCRLean/ActualIdealGluing.lean:30:0: automatically included section variable(s) unused in theorem `PCRLean.ActualIdealGluing.generator_mem`:
  [Fintype ι]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype ι] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [8477/8487] Built PCRLean.CoordinateBlowupChart (7.0s)
warning: PCRLean/CoordinateBlowupChart.lean:82:0: automatically included section variable(s) unused in theorem `PCRLean.CoordinateBlowupChart.pivot_mem`:
  [DecidableEq ι]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq ι] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [8478/8487] Built PCRLean.DifferentialOrbitKernel (8.0s)
⚠ [8479/8487] Built PCRLean.CoordinateCentreProper (6.7s)
warning: PCRLean/CoordinateCentreProper.lean:53:2: Try `simp at hzero` instead of `simpa using hzero`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [8480/8487] Built PCRLean.LinearPacketIdeal (7.1s)
warning: PCRLean/LinearPacketIdeal.lean:150:0: automatically included section variable(s) unused in theorem `PCRLean.LinearPacketIdeal.packetIdeal_coordinateRows`:
  [Fintype τ]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype τ] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [8481/8487] Built PCRLean.Experimental.CoordinateCentreQuotient (7.5s)
warning: PCRLean/Experimental/CoordinateCentreQuotient.lean:57:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: PCRLean/Experimental/CoordinateCentreQuotient.lean:85:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [8482/8487] Built PCRLean.CoordinateRootPacket (6.7s)
warning: PCRLean/CoordinateRootPacket.lean:68:0: automatically included section variable(s) unused in theorem `PCRLean.CoordinateRootPacket.sourceIdeal_le_centre_pow`:
  [DecidableEq ι]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq ι] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [8483/8487] Built PCRLean.DifferentialOrbitClosure (4.8s)
warning: PCRLean/DifferentialOrbitClosure.lean:78:6: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [8484/8487] Built PCRLean.FunctionalPacketIdeal (4.2s)
✖ [8485/8487] Building PCRLean.LinearCoordinateChange (3.9s)
trace: .> LEAN_PATH=/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Cli/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/batteries/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Qq/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/aesop/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/importGraph/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/plausible/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/mathlib/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean /home/runner/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean /home/runner/work/ci-exercise/ci-exercise/PCRLean/LinearCoordinateChange.lean -o /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/LinearCoordinateChange.olean -i /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/LinearCoordinateChange.ilean -c /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/LinearCoordinateChange.c --setup /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/LinearCoordinateChange.setup.json --json
error: PCRLean/LinearCoordinateChange.lean:116:4: invalid 'calc' step, left-hand side is
  ∑ x,
    DFunLike.coe.{max (v + 1) (u + 1), u + 1, max (v + 1) (u + 1)} MvPolynomial.C
        ((F.functional i) (FunctionalPacketIdeal.basisVector x)) *
      ∑ j, MvPolynomial.C (F.vector j x) * MvPolynomial.X j : @MvPolynomial σ K Field.toSemifield.toCommSemiring
but is expected to be
  ∑ x,
    DFunLike.coe.{(max u v) + 1, (max u v) + 1, (max u v) + 1} F.inverse
        (MvPolynomial.C (FunctionalPacketIdeal.coefficientRow (F.functional i) x)) *
      ∑ x_1, MvPolynomial.C (F.vector x_1 x) * MvPolynomial.X x_1 : @MvPolynomial σ K Field.toSemifield.toCommSemiring
warning: PCRLean/LinearCoordinateChange.lean:113:31: This simp argument is unused:
  MvPolynomial.map_C

Hint: Omit it from the simp argument list.
  simp only [map_sum, map_mul, M̵v̵P̵o̵l̵y̵n̵o̵m̵i̵a̵l̵.̵m̵a̵p̵_̵C̵,̵inverse_X, inverseVariable, LinearPacketIdeal.linearPolynomial]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: PCRLean/LinearCoordinateChange.lean:157:4: Type mismatch: After simplification, term
  h
 has type
  (if i = j then 1 else 0) = ∑ x, F.vector x i * (F.functional x) (FunctionalPacketIdeal.basisVector j)
but is expected to have type
  ∑ x, F.vector x i * (F.functional x) (FunctionalPacketIdeal.basisVector j) = if j = i then 1 else 0
error: PCRLean/LinearCoordinateChange.lean:164:4: invalid 'calc' step, left-hand side is
  ∑ x,
    DFunLike.coe.{max (v + 1) (u + 1), u + 1, max (v + 1) (u + 1)} MvPolynomial.C (F.vector x i) *
      ∑ j,
        MvPolynomial.C ((F.functional x) (FunctionalPacketIdeal.basisVector j)) *
          MvPolynomial.X j : @MvPolynomial σ K Field.toSemifield.toCommSemiring
but is expected to be
  ∑ x,
    DFunLike.coe.{(max u v) + 1, (max u v) + 1, (max u v) + 1} F.forward (MvPolynomial.C (F.vector x i)) *
      ∑ i,
        MvPolynomial.C (FunctionalPacketIdeal.coefficientRow (F.functional x) i) *
          MvPolynomial.X i : @MvPolynomial σ K Field.toSemifield.toCommSemiring
warning: PCRLean/LinearCoordinateChange.lean:159:31: This simp argument is unused:
  MvPolynomial.map_C

Hint: Omit it from the simp argument list.
  simp only [map_sum, map_mul, M̵v̵P̵o̵l̵y̵n̵o̵m̵i̵a̵l̵.̵m̵a̵p̵_̵C̵,̵
  ̵ ̵ ̵ ̵ ̵forward_X, forwardVariable,
      FunctionalPacketIdeal.functionalPolynomial,
  ̵  ̵ ̵ ̵LinearPacketIdeal.linearPolynomial]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: Lean exited with code 1
Some required targets logged failures:
- PCRLean.LinearCoordinateChange
error: build failed
```

## u4-axioms.txt
```text
PCRLean/Experimental/LinearSplitCentreBlowupAudit.lean:1:0: error: object file '/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/Experimental/LinearSplitCentreBlowup.olean' of module PCRLean.Experimental.LinearSplitCentreBlowup does not exist
```
