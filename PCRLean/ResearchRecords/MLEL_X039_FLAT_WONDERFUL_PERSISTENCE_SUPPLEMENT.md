# MLEL-X039 Supplement

## Flat Wonderful Persistence and Generator-Only Passive Preparation

**Parent:** `MLEL-X039 / NTR-RFL`  
**Class:** `CANDIDATE GEOMETRIC COMPRESSION / OPEN REGULAR-FLAG EDGE`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 1. New compression

Let `X` be regular and let `A={C_i}` be a finite intersection-closed clean
arrangement of regular closed subschemes.  Let `M` be one passive owner.
Assume that `M` is normally flat along every generating carrier `C_i`.

Every nonempty stratum

```text
C_S = intersection_(i in S) C_i
```

is regular.  Fix `i in S`.  Then `C_S subset C_i` is a closed immersion between
regular locally Noetherian schemes and hence a regular immersion.  Hironaka
normal-flatness transitivity therefore gives

```text
M normally flat along C_i
-> M normally flat along C_S.
```

Thus passive preparation of the generators automatically prepares the entire
finite intersection arrangement.  One does not need an independent
flatification for every stratum.

---

# 2. Minimal-stratum nesting

Let `D` be a minimal nonempty stratum under inclusion.  For any other stratum
`C`, the intersection `D intersection C` is again a stratum.  If it is nonempty,
minimality of `D` forces

```text
D intersection C = D,
```

hence `D subset C`.  Therefore a deepest-first wonderful blowup interacts with
every remaining stratum in exactly one of two ways:

```text
D is disjoint from C,
or
D is a regular subcarrier of C.
```

There is no third clean-intersection case requiring a new transform formalism
at that stage.  The nested Regular-Flag Flat-Lift theorem is sufficient.

---

# 3. Induction through the wonderful word

Assume the Regular-Flag Flat-Lift theorem.  Blow up the minimal stratum `D`.

* A stratum disjoint from `D` is unchanged locally.
* If `D subset C`, the strict transform of `C` is `Bl_D(C)`, and the
  Regular-Flag Flat-Lift theorem transports the purified associated-graded
  owner portfolio from `C` to its strict transform.
* Carrier flatness kills every purification-grading exceptional-torsion layer.
* Hironaka transitivity prepares every new nonempty intersection stratum.
* Exceptional-monomial no-recharge prevents a later Cartier trace from creating
  a fresh passive defect.

The transformed arrangement is again a clean intersection arrangement, with
one fewer active minimal stratum in the current wonderful layer.  Induction on
the finite word gives passive legality for every centre in the complete
wonderful serialization.

---

# 4. Candidate theorem

> **Flat Wonderful Persistence Theorem.**  Let `A` be a finite
> symmetry-stable, intersection-closed clean arrangement of regular carriers in
> a regular Noetherian ambient scheme.  Let a finite passive owner portfolio be
> normally flat along every generating carrier.  Assume the sheafified
> Hironaka transitivity theorem, the all-chart Regular-Flag Flat-Lift theorem,
> and exceptional no-recharge.  Then every stratum of `A` is normally flat for
> every owner, and the symmetry-compatible deepest-first wonderful word
> consists entirely of passive-safe centres.  After each blowup the transformed
> arrangement satisfies the same statement.  No new passive flatification is
> required inside the wonderful word.

The theorem must also carry active marked legality, logarithmic/SNC legality,
nonidentity, source labels, and overlap identities before it can feed the full
joint-legality compiler.

---

# 5. Consequence for actual-centre synthesis

The passive branch can now be scheduled as follows.

```text
finite raw generator family
-> simultaneously legalize only the generators
-> complete the regular intersection arrangement
-> infer passive legality of every stratum by transitivity
-> execute the wonderful word
-> preserve legality by regular-flag lifting
-> no passive recharge.
```

This removes a potentially exponential family of independent passive
flatification tasks.  The full intersection arrangement remains necessary for
regularity, symmetry, boundary, contact, and wonderful serialization, but not
for repeated passive preparation.

---

# 6. Exact remaining obligations

```text
FWP-1  GENERATOR_TO_STRATUM_NORMAL_FLATNESS
       sheafified Hironaka transitivity for every finite owner;

FWP-2  MINIMAL_STRATUM_NESTING
       intersection closure plus minimality gives disjoint-or-contained;

FWP-3  WONDERFUL_TRANSFORM_CLEANNESS
       the deepest-first transform remains a clean arrangement;

FWP-4  REGULAR_FLAG_FLAT_LIFT
       exact all-chart transport for every containing stratum;

FWP-5  EXCEPTIONAL_NO_RECHARGE
       no purification or source-Cartier torsion returns;

FWP-6  SYMMETRY_AND_LEDGER_NATURALITY
       generator orbits, strata, sources, debts, and boundaries reenter without
       arbitrary choices or reset.
```

`FWP-2` is elementary finite order/intersection algebra.  `FWP-1` is standard
normal-flatness transitivity with a project-specific sheaf interface.  `FWP-4`
and `FWP-6` remain load-bearing.

---

# 7. Effect on the proof graph

The former node

```text
X039-G15 WONDERFUL_WORD_PASSIVE_HEREDITY
```

is refined to

```text
X039-G15A GENERATOR_ONLY_PASSIVE_PREPARATION
X039-G15B ALL_STRATA_PASSIVE_BY_HIRONAKA_TRANSITIVITY
X039-G15C DEEPEST_FIRST_DISJOINT_OR_NESTED_COVERAGE
X039-G15D WONDERFUL_WORD_PERSISTENCE_BY_REGULAR_FLAG_LIFT.
```

The highest-information cut remains the Regular-Flag Flat-Lift and no-reset
edges.  The new theorem reduces downstream multiplicity; it does not construct
the first flat generator family.

---

# 8. Truth boundary

```text
GENERATOR_ONLY_PASSIVE_PREPARATION_IDENTIFIED      = true
MINIMAL_STRATUM_NESTING_IDENTIFIED                 = elementary
HIRONAKA_TRANSITIVITY_INPUT_IDENTIFIED             = true
WONDERFUL_PASSIVE_PERSISTENCE_FORMULATED           = true

SHEAFIFIED_TRANSITIVITY_PROVED_IN_PROJECT          = false
REGULAR_FLAG_FLAT_LIFT_PROVED                      = false
WONDERFUL_ALL_CHART_NO_RESET_PROVED                = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```
