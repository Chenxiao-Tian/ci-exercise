# PCRLean exact formal frontier

This branch contains genuine Lean kernel checks. It does not contain a proof of arbitrary-dimensional resolution in positive characteristic.

## Verified backend

The following logical implication is kernel-checked:

1. every nonterminal state has a successor;
2. every successor is produced by a finite-type actual centre action carrying all declared legality, chart, overlap, reentry and rank certificates;
3. one fixed well-founded rank strictly decreases on every step;
4. terminal states are geometrically resolved.

Then every input reaches a resolved terminal state after finitely many steps, and no infinite branch exists.

The Lean declarations are:

- `PCRLean.ResolutionCompiler.Program.terminal_reachable`;
- `PCRLean.ResolutionCompiler.Program.no_infinite_execution`;
- `PCRLean.ConditionalMaster.System.every_input_resolves`;
- `PCRLean.ConditionalMaster.System.every_step_all_gates`.

## Verified local algebra

- odd-cusp active and sibling chart identities;
- tame ramified quadratic collision identity and debt recurrence;
- Artin-Schreier collision update and finite parameter measure;
- principal Frobenius-root active and sibling chart identities;
- iterated Frobenius additivity and cleaning identity;
- mark-two containment for binary quadratic centre packets;
- finite-source generation and no-recharge logic;
- clone, fresh-birth, radical/support and fixed-direction-depth no-go theorems;
- affine Rees algebra coefficient criterion and finite-type foundation.

## Exact unresolved Lean goals

### U1. Arbitrary-input packetization

Construct a finite, intrinsic, presentation-independent state from an arbitrary differential Rees algebra or marked ideal, compatible with smooth/etale base change, cleaning and integral-closure equivalence.

### U2. Actual-centre effectivity

From a singular/nonreduced direction packet, construct a finite-type ideal whose closed subscheme is regular, nonidentity, marked-permissible and SNC-compatible. Formal or completed centres are insufficient.

### U3. Joint legality

Prove that the same centre is permissible for all active owners and normal-flat/Tor-safe for every passive owner, or construct a finite certified centre word when no single centre exists.

### U4. Complete transform and hereditary reentry

Define scheme-level blowup, strict transform and controlled transform; prove every standard chart and overlap; reconstruct all packets after cleaning, saturation, normalization and integral closure without resetting ancestry, source or debt.

### U5. Fully quasilinear kernel

Resolve the characteristic-two rank-zero polar chamber by an actual regular radicial core or prove a structural reduction to a lower certified class.

### U6. Geometric birth realization

Show every new jump-capable identity is a source merge, a paid birth from one fixed finite ancestor carrier, or accompanies an earlier strict geometric drop. Prove no split and no clone on every chart.

### U7. Immediate defect

Produce a projection-free finite-type actual centre word changing the intrinsic pro-isomorphism class, rather than using approximation stage as a rank.

### U8. Globalization

Glue local actual ideals, handle symmetry without arbitrary singleton choices, serialize finitely, prove smooth/etale functoriality, and derive principalization, embedded resolution and nonembedded resolution.

## Non-negotiable rule

No item U1-U8 may be crossed by `axiom`, `sorry`, `admit`, an unproved typeclass instance, or an imported experimental MLE theorem. A complete proof exists in this branch only when all eight goals have kernel-checked constructions and the final `#print axioms` audit contains no project-specific assumptions.
