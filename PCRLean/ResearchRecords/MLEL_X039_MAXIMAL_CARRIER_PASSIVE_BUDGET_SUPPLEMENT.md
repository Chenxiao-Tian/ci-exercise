# MLEL-X039 Supplement

## Maximal-Carrier Passive Budgets and Source-Conservative Wonderful Persistence

**Parent:** `MLEL-X039 / NTR-RFL`  
**Class:** `CANDIDATE TERMINATION AND COMPILER COMPRESSION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 1. Maximal-carrier reduction

Let `A` be a finite intersection-closed family of nonempty regular carriers.
Order `A` by scheme-theoretic inclusion.  Let `Max(A)` be its finite set of
inclusion-maximal carriers.

Every `S in A` is contained in some `C in Max(A)`.  If a passive owner is
normally flat along every member of `Max(A)`, then Hironaka transitivity along
the regular immersion

```text
S subset C
```

implies normal flatness along `S`.

Hence the passive preparation gate for a clean finite arrangement is
concentrated on one finite antichain:

```text
normal flatness on Max(A)
-> normal flatness on every intersection stratum.
```

This is stronger than preparing the original generating family when some
generators are nested.  It is invariant under every automorphism of the
arrangement because `Max(A)` is intrinsic.

---

# 2. One passive charge per maximal source

Assign to each maximal carrier source `lambda` a Boolean enrolment state

```text
unprepared(lambda) / prepared(lambda)
```

and, while unprepared, a finite immutable flatifier-word height `h_lambda`.
The passive budget is the multiset

```text
P(A)=multiset { (dim C_lambda, h_lambda) | lambda unprepared }.
```

Order pairs lexicographically and use the Dershowitz--Manna multiset extension.
A nested legalization call strictly lowers carrier dimension; execution of one
word edge lowers `h_lambda`; completion removes the pair entirely.

After a maximal source is prepared:

```text
Hironaka transitivity
+ Regular-Flag Flat-Lift
+ exceptional no-recharge
```

forces every descendant stratum and every strict transform in the wonderful
word to inherit the prepared state.  It is forbidden to insert a fresh passive
charge for such a descendant.

---

# 3. Birth boundary

New passive charges may enter only through a genuine outer geometric birth:

```text
new intrinsic carrier source
with an actual support witness and lineage map.
```

They may not be created by:

```text
chart restriction,
overlap localization,
Cartier trace,
cleaning,
normalization,
intersection completion,
wonderful serialization,
or source relabelling.
```

Thus the passive budget interfaces directly with `TRM-01/02` finite-source
support and birth classification.  Within one centre-synthesis macro, the
budget is nonincreasing; across outer successors, every increase must be
charged to a typed birth event in the existing causal ledger.

---

# 4. Deepest-first persistence

Let `D` be a minimal nonempty stratum.  For any `C in A`, intersection closure
and minimality give

```text
D intersection C = empty
or
D subset C.
```

Therefore one deepest-first wonderful step has only two passive cases.

1. **Disjoint case.**  The owner and carrier portfolio are unchanged near `C`.
2. **Nested case.**  Regular-Flag Flat-Lift transports the prepared portfolio
   from `C` to `Bl_D(C)`; flatness kills purification torsion and transitivity
   prepares all new intersections.

Induction on the finite wonderful word preserves the zero passive budget.  No
new flatifier is scheduled after the maximal antichain has been prepared.

---

# 5. Candidate theorem

> **Maximal-Carrier Passive-Budget Theorem.**  Let a finite symmetry-stable,
> intersection-closed clean arrangement of regular carriers carry a finite
> passive owner portfolio.  Assume every inclusion-maximal carrier has been
> legalized once by a centre-enriched flatifier and that Hironaka
> transitivity, Regular-Flag Flat-Lift, exceptional no-recharge, and
> source-conservative overlap transport hold.  Then every stratum is passive
> legal, every centre in the symmetry-compatible wonderful word is passive
> legal, and the passive preparation budget remains empty throughout that
> word.  Any later nonempty passive budget must be accompanied by a genuine
> typed outer birth source.

The theorem does not supply the first flatifiers, active legality, boundary
SNC, contact cleaning, or outer birth finiteness.

---

# 6. Rank consequence

The local legalization rank can be replaced by the multiset

```text
P(A)
```

followed by

```text
Rees comparison defect,
contact profile,
Hasse/Fitting profile,
source/debt ledger,
SCC height,
remaining outer macro height.
```

There is no separate passive coordinate for every intersection stratum.  This
removes a potentially exponential family of rank entries and prevents a hidden
reset under wonderful completion.

---

# 7. Exact open obligations

```text
MPB-1  SHEAFIFIED_MAXIMAL_TO_STRATUM_TRANSITIVITY
MPB-2  REGULAR_FLAG_FLAT_LIFT
MPB-3  WONDERFUL_TRANSFORM_CLEANNESS
MPB-4  SOURCE_CONSERVATIVE_MAXIMAL_CARRIER_TRANSPORT
MPB-5  NO_PASSIVE_BIRTH_FROM_INTERSECTION_COMPLETION
MPB-6  GENUINE_OUTER_PASSIVE_BIRTH_CLASSIFICATION
MPB-7  MULTISET_PASSIVE_BUDGET_STRICTNESS
```

`MPB-1` is standard local normal-flatness mathematics with an open project
interface.  `MPB-2`, `MPB-4`, and `MPB-6` are load-bearing.

---

# 8. Truth boundary

```text
MAXIMAL_ANTICHAIN_REDUCTION_IDENTIFIED             = true
PASSIVE_BUDGET_MULTISEt_IDENTIFIED                 = true
WONDERFUL_NO_NEW_PASSIVE_CHARGE_FORMULATED         = true

SHEAFIFIED_TRANSITIVITY_PROVED_IN_PROJECT          = false
REGULAR_FLAG_FLAT_LIFT_PROVED                      = false
SOURCE_CONSERVATIVE_PASSIVE_BIRTH_THEOREM_PROVED   = false
GLOBAL_TERMINATION_PROVED                          = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```
