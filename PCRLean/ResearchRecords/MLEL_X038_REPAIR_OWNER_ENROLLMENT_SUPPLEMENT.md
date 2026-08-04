# MLEL-X038 Final Structural Supplement

## Repair-Owner Enrollment, Bimodal Regular-Flag Transport, and Cartier-Trace Debt

**Parent:** `MLEL-X038 / TVF-ANC`  
**Refined candidate label:** `MLEL-X038 / TVF-ROE`  
**Status:** `COUNTEREXAMPLE-DRIVEN OWNER-SEMANTICS CORRECTION / OPEN_GAP`  
**Date:** 2026-08-04

---

# 1. Executive correction

The affine normal-cone flatifier cannot be inserted into the passive portfolio
before it has done its job.  A centre used to repair a nonflat module is often
not Tor-safe for that module.  Requiring passive safety before repair would
forbid the only centre that removes the defect.

The owner grammar must therefore distinguish:

```text
ACTIVE OWNER
  a marked ideal whose centre must satisfy a power-containment certificate;

PASSIVE OWNER
  a module already enrolled for exact Tor-safe, normal-flat transport;

REPAIR OWNER
  a finite module or coherent sheaf whose source-labelled strict transform is
  intentionally being changed by a flatification/contact/Cartier-trace word;

DISCHARGED OWNER
  a zero defect or a completed source obligation.
```

A repair owner is promoted to passive only after its transformed module has the
required flatness certificate.  A generically zero repair defect is discharged
once flat-kill proves that its transform is zero.

This correction preserves the final theorem semantics: every centre must be
Tor-safe for every **passive** owner.  It does not require a centre to be
Tor-safe for a repair owner whose strict transform is intentionally changing.

---

# 2. Minimal no-go for premature passive enrollment

Let

```text
R=k[x,z],
C=V(x),
D=V(x,z),
M=R/(z).
```

The associated graded module of `M` along `C` has every homogeneous piece
isomorphic to `k[z]/(z)`, hence is not flat over `C`.  The only nonempty proper
regular centre in its bad locus is the point `D`.

But

```text
Tor_1^R(M,R/(x,z)) ~= k
```

by tensoring the resolution

```text
0 -> R --z--> R -> M -> 0
```

with `R/(x,z)`.  Therefore `D` is not passive-Tor-safe for `M`.

Nevertheless, blowing up `D` separates the strict transforms of `V(z)` and
`C`; the transformed module vanishes along the transformed carrier, and its
new associated graded module is zero and flat.

Hence:

```text
prematurely classify M as passive
-> the only repairing centre is forbidden;

classify M as repair
-> the trace blowup is allowed and completes the repair.
```

This is a theorem-semantics issue, not merely an implementation choice.

---

# 3. The universal contact family refutes one-step repair transport

Let

```text
R=k[x,y],
C=V(x),
D=V(x,y),
M_m=R/(x-y^m),  m>=2.
```

On `C`, multiplication by `x` on `M_m` is multiplication by `y^m`.  Thus

```text
gr_C(M_m)_a ~= y^(ma)k[y]/y^(m(a+1))k[y].
```

The full associated-graded module is uniformly `y^m`-power torsion.  Since the
blowup of the Cartier centre `(y)` on the curve `C` is the identity with that
specified centre, its centre-enriched strict transform is zero.

Blow up the ambient point `D`.  On the `y`-chart write `x=yt`.  The strict
transform of `M_m` is

```text
t-y^(m-1)=0,
```

while the strict transform of `C` is `t=0`.  Therefore

```text
gr_(C')(M_m')_a
  ~= y^((m-1)a)k[y]/y^((m-1)(a+1))k[y],
```

which is nonzero for `m>1`.

Consequently the one-step assertion

```text
associated graded after ambient strict transform
=
carrier strict transform of the old associated graded
```

is false for a repair owner, even for a regular zero-dimensional flag centre.
No recursive modification of the point `D` can repair the one-step edge,
because `D` has no proper nonempty subcentre.

What is true is the strict contact law

```text
m -> m-1.
```

After finitely many ambient Cartier-trace steps the contact disappears and the
ambient associated graded agrees with the carrier target zero.

---

# 4. Bimodal Regular-Flag theorem

The former universal Regular-Flag Legal-Lift target must split into two modes.

## 4.1 Passive mode

> **Passive Regular-Flag Exact-Transport Theorem, target.**  Let
> `D subset C subset X` be a flag of regular immersions.  Let `P` be a passive
> owner for which `D` carries the full Tor-safety, normal-flatness, and
> logarithmic legality certificates.  Then blowing up `X` in `D` transports the
> affine normal-cone module of `P` exactly, with the canonical exceptional
> grading twist, on every chart and overlap.  In the controlled-core
> factorization, `ker(alpha)`, `ker(beta)`, and `coker(beta)` vanish.

This is the intended HER-02/HER-03 edge and remains open in the full scheme
interface.

## 4.2 Repair mode

> **Repair Regular-Flag Debt Theorem, target.**  Let `F` be a repair owner with
> immutable carrier source ideal and pure-transform target.  Under a regular
> ambient trace blowup, the controlled-core factorization need not be exact.
> Its three defects admit a finite source-labelled Cartier/contact debt packet.
> Either the target pure transform is already realized, or an intrinsic contact
> exponent, saturation exponent, Fitting-support coordinate, or carrier-support
> dimension strictly decreases.  The packet does not create an unfinanced new
> source.

The tangent family above is the scalar model of the repair theorem.

---

# 5. Cartier-trace debt

After lower-dimensional principalization, a repair source ideal on the carrier
is monomial:

```text
J O_(C') = product_alpha E_alpha^(a_alpha).
```

For a finite repair module `F`, the sections supported on each Cartier divisor
`E_alpha` are killed by a finite power.  Define the trace-debt exponent

```text
tau_alpha(F)
  = min{e | I_(E_alpha)^e H^0_(E_alpha)(F)=0}.
```

Noetherianity makes every `tau_alpha` finite.  The proposed debt packet is the
finite multiset

```text
TD(F)=multiset_alpha (support dimension, tau_alpha, Fitting profile, source age).
```

An ambient trace blowup along the regular image of `E_alpha` must satisfy one
of:

```text
1. the relevant source-pure transform is realized;
2. tau_alpha drops by one;
3. the support dimension of the top debt piece drops;
4. a Fitting/kernel coordinate drops.
```

The debt may be relabelled by exceptional divisors, but its immutable source
prevents recharge.  This is the module-valued extension of the previously
formalized scalar contact rule `m -> m-1`.

---

# 6. Repair-to-passive enrollment

A repair macro has three terminal outputs.

```text
FLAT ENROLLMENT
  the transformed repair owner is flat over the carrier and is promoted to the
  passive portfolio;

ZERO DISCHARGE
  the repair owner is generically zero and flat-kill on a reduced carrier
  proves it is zero;

LOWER-DIMENSIONAL REPAIR
  the remaining defect is supported on a strict lower-dimensional carrier and
  is sent to the outer induction.
```

Promotion is one-way.  A passive owner cannot silently return to repair status;
that would reset the causal rank.  If a later centre violates its passive
certificate, that centre is illegal and must itself be legalized before use.

---

# 7. Correct dimension-strict compiler

The carrier algorithm becomes:

```text
RepairLegalize_n(C):
  1. retain already-enrolled passive owners P;
  2. construct the affine normal/mixed-Rees repair portfolio F;
  3. choose one centre-enriched admissible flatifier/principalizer for F on C;
  4. factor its source ideals into a lower-dimensional regular carrier word;
  5. for each word centre D:
       a. recursively legalize D only for P, the boundary, active marks, and
          immutable source ledgers;
       b. transport P by the passive regular-flag theorem;
       c. transform F in repair mode and register finite trace debt;
       d. execute the finite debt-cleaning word;
  6. at the source-word endpoint, enroll the flat output or discharge the zero
     output;
  7. return a jointly legal carrier.
```

This avoids two circularities simultaneously:

```text
no requirement that a repair centre already be Tor-safe for the object it is
repairing;

no repeated unranked same-dimensional reflattification.
```

Nested centre legalization still lowers carrier dimension.  Repair cleaning is
controlled by the finite trace-debt multiset.

---

# 8. Revised rank

The local macro rank should be ordered as

```text
carrier dimension,
repair phase,
trace-debt multiset,
passive legality defect,
anchor contact,
Fitting/Hasse profile,
source/debt age,
SCC height,
remaining word height.
```

The key ordering rule is:

```text
carrier dimension precedes everything;
within one carrier, repair debt precedes passive enrollment;
a promotion from repair to passive is a strict phase drop;
zero discharge removes the owner;
source age prevents debt recharge.
```

The existing Lean arithmetic for dimension/contact/debt remains reusable, but
the repair phase and multiset debt require new declarations.

---

# 9. Revised decisive cut

```text
ROE-A  PASSIVE_REGULAR_FLAG_EXACT_TRANSPORT
       exact transport for already-enrolled passive owners;

ROE-B  REPAIR_REGULAR_FLAG_TRACE_DEBT
       finite debt packet and strict contact/saturation/Fitting descent;

ROE-C  CENTRE_ENRICHED_FLATIFIER_FACTORIZATION
       lower-dimensional regular source word and ambient trace realization;

ROE-D  REPAIR_TO_PASSIVE_ENROLLMENT_NO_RESET
       one-way promotion or zero discharge with complete ledger transport.
```

This cut is more precise than requiring one universal regular-flag equality.
It is also compatible with the final theorem's passive-safety semantics.

---

# 10. Publication consequence

The maximum-likelihood Paper III should now be titled

```text
Affine Normal-Cone Repair,
Tor--Valabrega Factorization,
and Hereditary Owner Enrollment.
```

Paper IV absorbs Cartier-trace debt into its causal termination theorem.  The
central page estimate moves from `552` to a range `552--560`; the modal point is
`556` dense Annals/AMS-equivalent pages.

---

# 11. Truth boundary

```text
PREMATURE_PASSIVE_ENROLLMENT_COUNTEREXAMPLE       = proved by explicit algebra
ONE_STEP_REPAIR_REGULAR_FLAG_LIFT                 = false
REPAIR_OWNER_PHASE_REQUIRED                       = true
BIMODAL_REGULAR_FLAG_ARCHITECTURE_IDENTIFIED      = true
CARTIER_TRACE_DEBT_PACKET_IDENTIFIED              = candidate
REPAIR_TO_PASSIVE_ENROLLMENT_IDENTIFIED           = candidate

PASSIVE_REGULAR_FLAG_EXACT_TRANSPORT_PROVED       = false
REPAIR_TRACE_DEBT_STRICT_DESCENT_PROVED           = false
CENTRE_ENRICHED_FLATIFIER_FACTORIZATION_PROVED    = false
REPAIR_ENROLLMENT_NO_RESET_PROVED                 = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED        = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION        = false
FORMAL_GLOBAL_STATUS                              = OPEN_GAP
```
