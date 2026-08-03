# PCRLean exact formal frontier

This branch contains genuine Lean kernel checks. It does not contain a proof of arbitrary-dimensional resolution in positive characteristic.

## Verified Hasse--Morita core layer

On a declared realized finite product Frobenius frame, the following implications are kernel-checked:

1. the recursive finite packet splits into multiplication and genuine Hasse indices;
2. separate passive stability under those two index classes implies stability under the full packet;
3. finite Hasse matrix-unit generation forces a passive block submodule to descend from one common row submodule;
4. active Hasse-only saturation and passive Morita descent can therefore be performed simultaneously;
5. over a Noetherian base, a proper active saturation yields a proper finitely generated descended core together with the passive row core.

The principal declarations are:

- `PCRLean.HMCSCCD.fullPacket_stable_of_split_stable`;
- `PCRLean.HMCSCCD.passive_eq_fromRowModule_of_split_stable`;
- `PCRLean.HMCSCCD.exists_active_passive_core`;
- `PCRLean.HMCSCCD.exists_proper_fg_active_passive_core`.

These statements do not construct a realized Frobenius frame for an arbitrary singularity, prove that the descended core is regular, or establish arbitrary passive Tor safety.

## Verified source-causal backend

A fixed-ancestor Noetherian trace module can be coupled lexicographically to the certified finite-source generational rank. An accepted transition is either a strict new-trace event or a source-conservative `GenStep`. The resulting relation is well founded.

The declarations are:

- `PCRLean.HMCSCCD.causalRankLt_wellFounded`;
- `PCRLean.HMCSCCD.causalRankStep_wellFounded`;
- `PCRLean.HMCSCCD.CausalProgram.terminal_reachable`;
- `PCRLean.HMCSCCD.CausalProgram.no_infinite_execution`.

For a supplied geometric system whose steps carry actual finite-type ideal, regularity, owner permissibility, passive safety, SNC boundary, all-chart, overlap, hereditary-reentry, nonidentity and rank certificates, Lean also verifies finite resolution and excludes an infinite branch:

- `PCRLean.HMCSCCD.GatedSystem.every_input_resolves`;
- `PCRLean.HMCSCCD.GatedSystem.every_step_all_gates`;
- `PCRLean.HMCSCCD.GatedSystem.no_infinite_branch`.

This is a conditional compiler. It does not prove universal existence of the gated geometric system or universal source-witness realization.

## Earlier verified backend

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
- finite multiplication--Hasse packet generation of matrix units;
- finite-free ideal descent and Hasse-only core descent;
- passive block Morita descent under the lifted finite packet;
- mark-two containment for binary quadratic centre packets;
- finite-source generation and no-recharge logic;
- clone, fresh-birth, radical/support and fixed-direction-depth no-go theorems;
- affine Rees algebra coefficient criterion and finite-type foundation.

## Exact unresolved Lean goals

### U1. Arbitrary-input packetization and gluing

Construct a finite, intrinsic, presentation-independent state from an arbitrary differential Rees algebra or marked ideal, compatible with smooth/etale base change, cleaning and integral-closure equivalence. Prove that local Hasse saturations, active cores and passive Morita cores glue independently of the chosen Frobenius frame.

### U2. Actual-centre effectivity

From an arbitrary proper Frobenius core or singular/nonreduced direction packet, construct a finite-type ideal whose closed subscheme is regular, nonidentity, marked-permissible and SNC-compatible. Remove the split-coordinate and root-equivalence hypotheses of the restricted `MLEL-002 / FCR-GEO` chamber by a Fitting/flattening and descent theorem. Formal or completed centres are insufficient.

### U3. Joint legality

Prove that the same centre is permissible for all active owners and normal-flat/Tor-safe for every passive owner, or construct a finite certified centre word when no single centre exists. The verified passive Morita row core is an algebraic descent result, not yet universal Tor safety.

### U4. Complete transform and hereditary reentry

Define scheme-level blowup, strict transform and controlled transform; prove every standard chart and overlap; reconstruct active cores, passive row cores and all ledgers after cleaning, saturation, normalization and integral closure without resetting ancestry, source or debt.

### U5. Fully quasilinear kernel

Resolve the characteristic-two rank-zero polar chamber by an actual regular radicial core or prove a structural reduction to a lower certified class.

### U6. Geometric birth realization

Show every new jump-capable identity is a source merge, a paid birth from one fixed finite ancestor carrier, or accompanies an earlier strict geometric drop. Prove no split and no clone on every chart. The source-causal backend proves termination after this classification is supplied; it does not construct the classification geometrically.

### U7. Immediate defect

Produce a projection-free finite-type actual centre word changing the intrinsic pro-isomorphism class, rather than using approximation stage as a rank.

### U8. Globalization

Glue local actual ideals, handle symmetry without arbitrary singleton choices, serialize finitely, prove smooth/etale functoriality, and derive principalization, embedded resolution and nonembedded resolution.

## Current MLE architecture after MLEL-M004

The highest-posterior proof chain is now:

```text
intrinsic finite Frobenius frame
-> multiplication/Hasse matrix-unit generation
-> simultaneous active Hasse core and passive Morita row core
-> actual regular owner-safe centre word
-> all-chart source-conservative reentry
-> Noetherian trace / finite-source causal descent
-> finite global serialization
-> principalization and resolution.
```

Only the finite-frame algebraic core and conditional causal backend are certified in the general abstract forms stated above. Universal geometric realization remains open.

## PCR-JUMP-LEAN 2.0 bridge decomposition

The baseline method protocol `PCR-JUMP-LEAN 2.0 / MLEL-A002-JUMP2` refines the open geometric middle without promoting any experimental theorem. Its default candidate chain is:

```text
intrinsic finite Frobenius--Hasse packet
-> finite conormal evaluation morphism
-> finite Fitting determinant atlas
-> split finite-projective quotient on each determinant chart
-> intrinsic kernel ideal sheaf
-> actual regular centre or finite centre word
-> joint legality
-> hereditary all-chart transform
-> causal source-support ledger
-> global well-founded compiler.
```

The three primary missions are:

```text
IFCCS  Intrinsic Fitting--Conormal Centre Sheaf
HKITF  Hereditary Kernel-Ideal Transform Functor
CSCN   Causal Source Cosheaf and Noetherian Ledger
```

The rank-zero fallback is:

```text
RZRC    Rank-Zero Radicial Core
```

These are candidate bridge programs. They may guide Experimental work but cannot be used as Lean premises in the official baseline.

## Non-negotiable rule

No item U1-U8 may be crossed by `axiom`, `sorry`, `admit`, an unproved typeclass instance, or an imported experimental MLE theorem. A complete proof exists in this branch only when all eight goals have kernel-checked constructions and the final `#print axioms` audit contains no project-specific assumptions.

Protocol adoption also imposes:

```text
no stale CI evidence
no Experimental-to-Certified import
no theorem promotion without explicit user authorization
no paper/Lean semantic weakening
```

Current global status: `OPEN_GAP`.
