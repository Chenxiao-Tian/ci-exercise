# U6 Causal Ledger CI Result

- source commit: `424195b3b972f0df07df48aa225bc4f4baa1c111`
- workflow run: `30777077766`
- placeholder rejection: success
- build: failure
- axiom audit: failure

## u6-placeholders.txt
```text
```

## u6-build.txt
```text
✔ [8475/8478] Built PCRLean.GenerationalRank (487ms)
✔ [8476/8478] Built PCRLean.SourcePartition (3.0s)
⚠ [8477/8478] Built PCRLean.Experimental.CausalEventPacking (3.9s)
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
✖ [8478/8478] Building PCRLean.Experimental.CausalEventLedger (3.7s)
trace: .> LEAN_PATH=/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Cli/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/batteries/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/Qq/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/aesop/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/importGraph/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/plausible/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/packages/mathlib/.lake/build/lib/lean:/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean /home/runner/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean /home/runner/work/ci-exercise/ci-exercise/PCRLean/Experimental/CausalEventLedger.lean -o /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/Experimental/CausalEventLedger.olean -i /home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/Experimental/CausalEventLedger.ilean -c /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/Experimental/CausalEventLedger.c --setup /home/runner/work/ci-exercise/ci-exercise/.lake/build/ir/PCRLean/Experimental/CausalEventLedger.setup.json --json
warning: PCRLean/Experimental/CausalEventLedger.lean:83:0: automatically included section variable(s) unused in theorem `PCRLean.Experimental.CausalEventLedger.Birth.used_child`:
  [Fintype Source]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype Source] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: PCRLean/Experimental/CausalEventLedger.lean:92:36: This simp argument is unused:
  and_left_comm

Hint: Omit it from the simp argument list.
  simp [State.unused, B.used_child, a̵n̵d̵_̵l̵e̵f̵t̵_̵c̵o̵m̵m̵,̵ ̵and_comm, and_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: PCRLean/Experimental/CausalEventLedger.lean:92:61: This simp argument is unused:
  and_assoc

Hint: Omit it from the simp argument list.
  simp [State.unused, B.used_child, and_left_comm, and_comm,̵ ̵a̵n̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: PCRLean/Experimental/CausalEventLedger.lean:98:6: Unknown identifier `B.unused_child`
error: PCRLean/Experimental/CausalEventLedger.lean:97:46: unsolved goals
Source : Type u
inst✝¹ : Fintype Source
inst✝ : DecidableEq Source
parent child : State
⊢ child.unused.card < parent.unused.card
error: PCRLean/Experimental/CausalEventLedger.lean:129:19: Invalid field notation: Function `Birth.unused_card_decreases` does not have a usable parameter of type `Birth ...` for which to substitute `B`

Note: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation
error: Lean exited with code 1
Some required targets logged failures:
- PCRLean.Experimental.CausalEventLedger
error: build failed
```

## u6-axioms.txt
```text
PCRLean/Experimental/CausalEventLedgerAudit.lean:1:0: error: object file '/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/Experimental/CausalEventLedger.olean' of module PCRLean.Experimental.CausalEventLedger does not exist
```
