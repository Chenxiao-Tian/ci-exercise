# PCR U2 Exact CI Certificate

- source commit: `e89b6adf9cf6c3a852de925d5cd09dd7285ae436`
- workflow run: `30777064802`
- generated at: `2026-08-03T03:36:30Z`

| Gate | Outcome |
|---|---|
| install | success |
| dependencies | success |
| placeholder rejection | success |
| commutative-ring split frames | failure |
| full linear coordinate automorphism | failure |
| transported linear centre | failure |
| causal event packing | success |
| intrinsic split-surjection quotient | success |
| automatic free-target splitting | success |
| intrinsic regular centre | success |
| finite-free symmetric algebra | failure |
| biorthogonal regular centre | failure |
| target gauge invariance | success |
| source-target centre transport | failure |
| unified axiom audit | failure |

## Failure tails

### 00-lake-update.txt
```text
info: downloading https://releases.lean-lang.org/lean4/v4.30.0/lean-4.30.0-linux.tar.zst
info: installing /home/runner/.elan/toolchains/leanprover--lean4---v4.30.0
info: PCRLean: no previous manifest, creating one from scratch
info: leanprover-community/mathlib: cloning https://github.com/leanprover-community/mathlib4
info: leanprover-community/mathlib: checking out revision 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
info: toolchain not updated; already up-to-date
info: plausible: cloning https://github.com/leanprover-community/plausible
info: plausible: checking out revision 'a456461b368b71d2accd95234832cd9c174b5437'
info: LeanSearchClient: cloning https://github.com/leanprover-community/LeanSearchClient
info: LeanSearchClient: checking out revision 'c5d5b8fe6e5158def25cd28eb94e4141ad97c843'
info: importGraph: cloning https://github.com/leanprover-community/import-graph
info: importGraph: checking out revision '515cf9d0c00ece5e661f6de4326a53dedc1e8ea1'
info: proofwidgets: cloning https://github.com/leanprover-community/ProofWidgets4
info: proofwidgets: checking out revision 'a84b3e2475d5c5ab979567b1ad8aea21b764bcf8'
info: aesop: cloning https://github.com/leanprover-community/aesop
info: aesop: checking out revision '558915ae105bfd8074e22d597613d1961822adc2'
info: Qq: cloning https://github.com/leanprover-community/quote4
info: Qq: checking out revision 'a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c'
info: batteries: cloning https://github.com/leanprover-community/batteries
info: batteries: checking out revision '32dc18cde3684679f3c003de608743b57498c56f'
info: Cli: cloning https://github.com/leanprover/lean4-cli
info: Cli: checking out revision '6b907cf12b2e445ccb7c24bc208ef04a1f39e84c'
info: mathlib: running post-update hooks
✔ [3/25] Built Cache.Init (329ms)
✔ [4/25] Built Cache.Lean (436ms)
✔ [5/25] Built Cache.Init:c.o (112ms)
✔ [6/25] Built Cache.Lean:c.o (168ms)
✔ [14/25] Built Batteries.Data.String.Basic:c.o (175ms)
✔ [15/25] Built Batteries.Data.String.Matcher:c.o (243ms)
✔ [16/25] Built Batteries.Data.Array.Match:c.o (309ms)
✔ [17/25] Built Cache.IO (1.8s)
✔ [18/25] Built Cache.Hashing (883ms)
✔ [19/25] Built Cache.Hashing:c.o (545ms)
✔ [20/25] Built Cache.IO:c.o (1.5s)
✔ [21/25] Built Cache.Requests (2.3s)
✔ [22/25] Built Cache.Main (976ms)
✔ [23/25] Built Cache.Main:c.o (629ms)
✔ [24/25] Built Cache.Requests:c.o (2.2s)
✔ [25/25] Built cache:exe (682ms)
Current branch: HEAD
Using cache (Azure) from origin: (some leanprover-community/mathlib4)
Attempting to download 8459 file(s) from leanprover-community/mathlib4 cache
Downloaded: 1 file(s) [attempted 1/8459 = 0%, 45 KB/s], Decompressed: 0Downloaded: 18 file(s) [attempted 18/8459 = 0%, 57 KB/s], Decompressed: 15Downloaded: 164 file(s) [attempted 164/8459 = 1%, 2789 KB/s], Decompressed: 32Downloaded: 368 file(s) [attempted 368/8459 = 4%, 4019 KB/s], Decompressed: 32Downloaded: 560 file(s) [attempted 560/8459 = 6%, 3070 KB/s], Decompressed: 32Downloaded: 848 file(s) [attempted 848/8459 = 10%, 7877 KB/s], Decompressed: 112Downloaded: 1052 file(s) [attempted 1052/8459 = 12%, 608 KB/s], Decompressed: 112Downloaded: 1283 file(s) [attempted 1283/8459 = 15%, 1957 KB/s], Decompressed: 112Downloaded: 1497 file(s) [attempted 1497/8459 = 17%, 345 KB/s], Decompressed: 112Downloaded: 1708 file(s) [attempted 1708/8459 = 20%, 958 KB/s], Decompressed: 112Downloaded: 1907 file(s) [attempted 1907/8459 = 22%, 4665 KB/s], Decompressed: 112Downloaded: 2108 file(s) [attempted 2108/8459 = 24%, 450 KB/s], Decompressed: 112Downloaded: 2359 file(s) [attempted 2359/8459 = 27%, 15468 KB/s], Decompressed: 112Downloaded: 2578 file(s) [attempted 2578/8459 = 30%, 3398 KB/s], Decompressed: 112Downloaded: 2799 file(s) [attempted 2799/8459 = 33%, 1662 KB/s], Decompressed: 112Downloaded: 3019 file(s) [attempted 3019/8459 = 35%, 7055 KB/s], Decompressed: 112Downloaded: 3250 file(s) [attempted 3250/8459 = 38%, 3898 KB/s], Decompressed: 112Downloaded: 3454 file(s) [attempted 3454/8459 = 40%, 2168 KB/s], Decompressed: 112Downloaded: 3669 file(s) [attempted 3669/8459 = 43%, 3498 KB/s], Decompressed: 112Downloaded: 3826 file(s) [attempted 3826/8459 = 45%, 9566 KB/s], Decompressed: 112Downloaded: 3997 file(s) [attempted 3997/8459 = 47%, 1262 KB/s], Decompressed: 112Downloaded: 4179 file(s) [attempted 4179/8459 = 49%, 601 KB/s], Decompressed: 112Downloaded: 4330 file(s) [attempted 4330/8459 = 51%, 4581 KB/s], Decompressed: 112Downloaded: 4531 file(s) [attempted 4531/8459 = 53%, 22014 KB/s], Decompressed: 112Downloaded: 4699 file(s) [attempted 4699/8459 = 55%, 19908 KB/s], Decompressed: 112Downloaded: 4939 file(s) [attempted 4939/8459 = 58%, 1477 KB/s], Decompressed: 112Downloaded: 5182 file(s) [attempted 5182/8459 = 61%, 5130 KB/s], Decompressed: 112Downloaded: 5386 file(s) [attempted 5386/8459 = 63%, 4586 KB/s], Decompressed: 112Downloaded: 5627 file(s) [attempted 5627/8459 = 66%, 1948 KB/s], Decompressed: 112Downloaded: 5856 file(s) [attempted 5856/8459 = 69%, 10792 KB/s], Decompressed: 751Downloaded: 6086 file(s) [attempted 6086/8459 = 71%, 6444 KB/s], Decompressed: 751Downloaded: 6312 file(s) [attempted 6312/8459 = 74%, 1181 KB/s], Decompressed: 751Downloaded: 6503 file(s) [attempted 6503/8459 = 76%, 1650 KB/s], Decompressed: 751Downloaded: 6742 file(s) [attempted 6742/8459 = 79%, 681 KB/s], Decompressed: 751Downloaded: 6969 file(s) [attempted 6969/8459 = 82%, 1335 KB/s], Decompressed: 751Downloaded: 7236 file(s) [attempted 7236/8459 = 85%, 5282 KB/s], Decompressed: 751Downloaded: 7445 file(s) [attempted 7445/8459 = 88%, 8874 KB/s], Decompressed: 751Downloaded: 7662 file(s) [attempted 7662/8459 = 90%, 7220 KB/s], Decompressed: 751Downloaded: 7861 file(s) [attempted 7861/8459 = 92%, 10402 KB/s], Decompressed: 751Downloaded: 8110 file(s) [attempted 8110/8459 = 95%, 3984 KB/s], Decompressed: 751Downloaded: 8335 file(s) [attempted 8335/8459 = 98%, 14133 KB/s], Decompressed: 751Downloaded: 8458 file(s) [attempted 8458/8459 = 99%, 10686 KB/s], Decompressed: 751Downloaded: 8459 file(s) [attempted 8459/8459 = 100%, 10686 KB/s], Decompressed: 751
Decompressed 8459 file(s)
Already decompressed 8459 file(s)
```

### 00-cache-get.txt
```text
Current branch: HEAD
Using cache (Azure) from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8459 file(s)
```

### 00-placeholders.txt
```text
```

### 01-split-frames-build.txt
```text
✔ [8475/8476] Built PCRLean.SplitConormalFrame (4.9s)
✖ [8476/8476] Building PCRLean.BiorthogonalSplitFrame (4.4s)
trace: .> LEAN_PATH=/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Cli/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/batteries/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Qq/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/aesop/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/importGraph/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/plausible/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/mathlib/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean /home/runner/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean /home/runner/work/ci-exercise/ci-exercise/PCRLean/BiorthogonalSplitFrame.lean -o /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/BiorthogonalSplitFrame.olean -i /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/BiorthogonalSplitFrame.ilean -c /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/BiorthogonalSplitFrame.c --setup /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/BiorthogonalSplitFrame.setup.json --json
error: PCRLean/BiorthogonalSplitFrame.lean:57:3: unexpected token 'section'; expected identifier
error: PCRLean/BiorthogonalSplitFrame.lean:72:18: unexpected token 'section'; expected ']'
error: PCRLean/BiorthogonalSplitFrame.lean:70:14: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:70:32: unsolved goals
case h
K : Type u
inst✝⁴ : CommRing K
V : Type v
inst✝³ : AddCommGroup V
inst✝² : Module K V
ι : Type w
inst✝¹ : Fintype ι
inst✝ : DecidableEq ι
F : Frame
a : ι → K
i : ι
⊢ { toFun := fun x i => (F.packet i) x, map_add' := ⋯, map_smul' := ⋯ } sorry i = a i
error: PCRLean/BiorthogonalSplitFrame.lean:72:26: unexpected token ','; expected command
error: PCRLean/BiorthogonalSplitFrame.lean:87:37: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:89:33: Application type mismatch: The argument
  a
has type
  ι
of sort `Type w` but is expected to have type
  ι → K
of sort `Type (max w u)` in the application
  eval_section F a
error: PCRLean/BiorthogonalSplitFrame.lean:95:13: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:100:54: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:123:0: Unexpected name `Frame` after `end`: The current section is unnamed

Hint: Delete the name `Frame` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵F̵r̵a̵m̵e̵
error: PCRLean/BiorthogonalSplitFrame.lean:127:0: Invalid name after `end`: Expected `Frame`, but found `BiorthogonalSplitFrame`
error: PCRLean/BiorthogonalSplitFrame.lean:128:0: Invalid name after `end`: Expected `Frame`, but found `PCRLean`
error: Lean exited with code 1
Some required targets logged failures:
- PCRLean.BiorthogonalSplitFrame
error: build failed
```

### 02-linear-coordinate-build.txt
```text
⚠ [8475/8480] Built PCRLean.ActualIdealGluing (4.6s)
warning: PCRLean/ActualIdealGluing.lean:30:0: automatically included section variable(s) unused in theorem `PCRLean.ActualIdealGluing.generator_mem`:
  [Fintype ι]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype ι] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [8476/8480] Built PCRLean.DifferentialOrbitKernel (5.3s)
⚠ [8477/8480] Built PCRLean.LinearPacketIdeal (4.8s)
warning: PCRLean/LinearPacketIdeal.lean:150:0: automatically included section variable(s) unused in theorem `PCRLean.LinearPacketIdeal.packetIdeal_coordinateRows`:
  [Fintype τ]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype τ] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [8478/8480] Built PCRLean.DifferentialOrbitClosure (5.0s)
warning: PCRLean/DifferentialOrbitClosure.lean:78:6: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [8479/8480] Built PCRLean.FunctionalPacketIdeal (4.6s)
✖ [8480/8480] Building PCRLean.LinearCoordinateChange (4.4s)
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

### 03-linear-centre-build.txt
```text
⚠ [8476/8484] Replayed PCRLean.LinearPacketIdeal
warning: PCRLean/LinearPacketIdeal.lean:150:0: automatically included section variable(s) unused in theorem `PCRLean.LinearPacketIdeal.packetIdeal_coordinateRows`:
  [Fintype τ]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype τ] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [8478/8484] Replayed PCRLean.DifferentialOrbitClosure
warning: PCRLean/DifferentialOrbitClosure.lean:78:6: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✖ [8480/8484] Building PCRLean.LinearCoordinateChange (4.6s)
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
⚠ [8481/8484] Built PCRLean.CoordinateBlowupChart (4.7s)
warning: PCRLean/CoordinateBlowupChart.lean:82:0: automatically included section variable(s) unused in theorem `PCRLean.CoordinateBlowupChart.pivot_mem`:
  [DecidableEq ι]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq ι] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [8482/8484] Built PCRLean.CoordinateCentreProper (4.7s)
warning: PCRLean/CoordinateCentreProper.lean:53:2: Try `simp at hzero` instead of `simpa using hzero`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [8483/8484] Built PCRLean.Experimental.CoordinateCentreQuotient (5.2s)
warning: PCRLean/Experimental/CoordinateCentreQuotient.lean:57:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: PCRLean/Experimental/CoordinateCentreQuotient.lean:85:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Some required targets logged failures:
- PCRLean.LinearCoordinateChange
error: build failed
```

### 04-causal-event-build.txt
```text
✔ [8475/8477] Built PCRLean.GenerationalRank (511ms)
✔ [8476/8477] Built PCRLean.SourcePartition (4.2s)
⚠ [8477/8477] Built PCRLean.Experimental.CausalEventPacking (4.3s)
warning: PCRLean/Experimental/CausalEventPacking.lean:45:0: automatically included section variable(s) unused in theorem `PCRLean.Experimental.CausalEventPacking.Section.chosenSource_mem`:
  [Fintype Source]
  [Fintype Event]
  [DecidableEq Source]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype Source] [Fintype Event] [DecidableEq Source] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: PCRLean/Experimental/CausalEventPacking.lean:50:0: automatically included section variable(s) unused in theorem `PCRLean.Experimental.CausalEventPacking.Section.source_owner_unique`:
  [Fintype Source]
  [Fintype Event]
  [DecidableEq Source]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype Source] [Fintype Event] [DecidableEq Source] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Build completed successfully (8477 jobs).
```

### 05-split-surjection-build.txt
```text
✔ [8475/8475] Built PCRLean.Experimental.SplitSurjectionSymmetricQuotient (5.7s)
Build completed successfully (8475 jobs).
```

### 06-surjective-free-build.txt
```text
⚠ [8476/8476] Built PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient (4.0s)
warning: PCRLean/Experimental/SurjectiveLinearMapSymmetricQuotient.lean:111:2: Try `simp at hzero` instead of `simpa using hzero`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (8476 jobs).
```

### 07-regular-centre-build.txt
```text
⚠ [8476/8477] Replayed PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient
warning: PCRLean/Experimental/SurjectiveLinearMapSymmetricQuotient.lean:111:2: Try `simp at hzero` instead of `simpa using hzero`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [8477/8477] Built PCRLean.Experimental.SurjectiveFreeRegularCentre (4.6s)
Build completed successfully (8477 jobs).
```

### 08-finite-free-symmetric-build.txt
```text
✖ [8474/8476] Running Mathlib.RingTheory.RegularLocalRing.Polynomial
error: no such file or directory (error code: 4294967294)
  file: /home/runner/work/ci-exercise/ci-exercise/.lake/packages/mathlib/Mathlib/RingTheory/RegularLocalRing/Polynomial.lean
✖ [8475/8476] Running PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular
error: PCRLean/Experimental/FiniteFreeSymmetricAlgebraRegular.lean: bad import 'Mathlib.RingTheory.RegularLocalRing.Polynomial'
Some required targets logged failures:
- Mathlib.RingTheory.RegularLocalRing.Polynomial
- PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular
error: build failed
```

### 09-biorthogonal-centre-build.txt
```text
✖ [8474/8482] Running Mathlib.RingTheory.RegularLocalRing.Polynomial
error: no such file or directory (error code: 4294967294)
  file: /home/runner/work/ci-exercise/ci-exercise/.lake/packages/mathlib/Mathlib/RingTheory/RegularLocalRing/Polynomial.lean
✖ [8475/8482] Running PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular
error: PCRLean/Experimental/FiniteFreeSymmetricAlgebraRegular.lean: bad import 'Mathlib.RingTheory.RegularLocalRing.Polynomial'
✖ [8476/8482] Running PCRLean.Experimental.BiorthogonalRegularCentre
error: PCRLean/Experimental/BiorthogonalRegularCentre.lean: bad import 'Mathlib.RingTheory.RegularLocalRing.Polynomial'
error: PCRLean/Experimental/BiorthogonalRegularCentre.lean: bad import 'PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular'
⚠ [8480/8482] Replayed PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient
warning: PCRLean/Experimental/SurjectiveLinearMapSymmetricQuotient.lean:111:2: Try `simp at hzero` instead of `simpa using hzero`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✖ [8482/8482] Building PCRLean.BiorthogonalSplitFrame (4.4s)
trace: .> LEAN_PATH=/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Cli/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/batteries/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Qq/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/aesop/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/importGraph/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/plausible/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/mathlib/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean /home/runner/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean /home/runner/work/ci-exercise/ci-exercise/PCRLean/BiorthogonalSplitFrame.lean -o /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/BiorthogonalSplitFrame.olean -i /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/BiorthogonalSplitFrame.ilean -c /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/BiorthogonalSplitFrame.c --setup /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/BiorthogonalSplitFrame.setup.json --json
error: PCRLean/BiorthogonalSplitFrame.lean:57:3: unexpected token 'section'; expected identifier
error: PCRLean/BiorthogonalSplitFrame.lean:72:18: unexpected token 'section'; expected ']'
error: PCRLean/BiorthogonalSplitFrame.lean:70:14: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:70:32: unsolved goals
case h
K : Type u
inst✝⁴ : CommRing K
V : Type v
inst✝³ : AddCommGroup V
inst✝² : Module K V
ι : Type w
inst✝¹ : Fintype ι
inst✝ : DecidableEq ι
F : Frame
a : ι → K
i : ι
⊢ { toFun := fun x i => (F.packet i) x, map_add' := ⋯, map_smul' := ⋯ } sorry i = a i
error: PCRLean/BiorthogonalSplitFrame.lean:72:26: unexpected token ','; expected command
error: PCRLean/BiorthogonalSplitFrame.lean:87:37: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:89:33: Application type mismatch: The argument
  a
has type
  ι
of sort `Type w` but is expected to have type
  ι → K
of sort `Type (max w u)` in the application
  eval_section F a
error: PCRLean/BiorthogonalSplitFrame.lean:95:13: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:100:54: Invalid field `section`: The environment does not contain `PCRLean.BiorthogonalSplitFrame.Frame.section`, so it is not possible to project the field `section` from an expression
  F
of type `Frame`
error: PCRLean/BiorthogonalSplitFrame.lean:123:0: Unexpected name `Frame` after `end`: The current section is unnamed

Hint: Delete the name `Frame` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵F̵r̵a̵m̵e̵
error: PCRLean/BiorthogonalSplitFrame.lean:127:0: Invalid name after `end`: Expected `Frame`, but found `BiorthogonalSplitFrame`
error: PCRLean/BiorthogonalSplitFrame.lean:128:0: Invalid name after `end`: Expected `Frame`, but found `PCRLean`
error: Lean exited with code 1
Some required targets logged failures:
- Mathlib.RingTheory.RegularLocalRing.Polynomial
- PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular
- PCRLean.Experimental.BiorthogonalRegularCentre
- PCRLean.BiorthogonalSplitFrame
error: build failed
```

### 10-target-gauge-build.txt
```text
⚠ [8476/8477] Replayed PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient
warning: PCRLean/Experimental/SurjectiveLinearMapSymmetricQuotient.lean:111:2: Try `simp at hzero` instead of `simpa using hzero`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [8477/8477] Built PCRLean.Experimental.IntrinsicCentreGaugeInvariance (4.7s)
warning: PCRLean/Experimental/IntrinsicCentreGaugeInvariance.lean:64:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (8477 jobs).
```

### 11-centre-transport-build.txt
```text
⚠ [8476/8477] Replayed PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient
warning: PCRLean/Experimental/SurjectiveLinearMapSymmetricQuotient.lean:111:2: Try `simp at hzero` instead of `simpa using hzero`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✖ [8477/8477] Building PCRLean.Experimental.IntrinsicCentreTransport (5.1s)
trace: .> LEAN_PATH=/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Cli/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/batteries/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Qq/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/aesop/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/importGraph/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/plausible/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/mathlib/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean /home/runner/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean /home/runner/work/ci-exercise/ci-exercise/PCRLean/Experimental/IntrinsicCentreTransport.lean -o /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/Experimental/IntrinsicCentreTransport.olean -i /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/Experimental/IntrinsicCentreTransport.ilean -c /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/Experimental/IntrinsicCentreTransport.c --setup /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/Experimental/IntrinsicCentreTransport.setup.json --json
error: PCRLean/Experimental/IntrinsicCentreTransport.lean:81:8: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?m.216 ∈ Ideal.comap ?m.213 ?m.214
in the target expression
  (fun x => (SymmetricAlgebra.ι R V₁) ↑x) x ∈ ↑(Ideal.comap (↑(symmetricEquiv sourceGauge)) (kernelIdeal q))

case a
R : Type u
inst✝⁸ : CommRing R
V₁ : Type v₁
V₂ : Type v₂
inst✝⁷ : AddCommGroup V₁
inst✝⁶ : Module R V₁
inst✝⁵ : AddCommGroup V₂
inst✝⁴ : Module R V₂
W₁ : Type w₁
W₂ : Type w₂
inst✝³ : AddCommGroup W₁
inst✝² : Module R W₁
inst✝¹ : AddCommGroup W₂
inst✝ : Module R W₂
sourceGauge : V₁ ≃ₗ[R] V₂
targetGauge : W₁ ≃ₗ[R] W₂
p : V₁ →ₗ[R] W₁
q : V₂ →ₗ[R] W₂
hcomm : ↑targetGauge ∘ₗ p = q ∘ₗ ↑sourceGauge
x : ↥p.ker
⊢ (fun x => (SymmetricAlgebra.ι R V₁) ↑x) x ∈ ↑(Ideal.comap (↑(symmetricEquiv sourceGauge)) (kernelIdeal q))
error: Lean exited with code 1
Some required targets logged failures:
- PCRLean.Experimental.IntrinsicCentreTransport
error: build failed
```

### 12-u2-axioms.txt
```text
PCRLean/Experimental/U2SingleCIAudit.lean:1:0: error: object file '/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/LinearCoordinateChange.olean' of module PCRLean.LinearCoordinateChange does not exist
```
