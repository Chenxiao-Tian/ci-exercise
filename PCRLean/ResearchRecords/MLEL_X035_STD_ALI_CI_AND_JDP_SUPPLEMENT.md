# MLEL-X035 / STD-ALI - CI and Joint-Defect Supplement

**Date:** 2026-08-04  
**Class:** `EXPERIMENTAL_GREEN_SLICE + CANDIDATE_GRAPH_SUPPLEMENT`  
**Global status:** `OPEN_GAP`  
**Theorem promotion:** none

## Exact clean-room result

The exact-snapshot workflow completed successfully:

```text
PR                                  = #45
base SHA                            = aae3698ea11a984d0e6ea45defa1eb0723414323
head SHA                            = 9a39e9791ffc066c0708d257dd0560f2310b848a
PR merge snapshot                   = d0ec4bd7c6709b18a369d2d8661ec118e06b92b4
workflow run                        = 30883563214
job                                 = 91909803813
conclusion                          = success
Lean                                = 4.30.0
mathlib revision                    = c5ea00351c28e24afc9f0f84379aa41082b1188f
artifact                            = 8882283865
artifact SHA-256                    = 1cf911fcc969966aaefe26bc49b0bc0a7290071329723c86896eccd1c99115a5
```

The run rejected placeholders/project axioms, built the official target,
built every new X035 module and the integrated index, ran the unified axiom
audit with no `sorryAx`, and uploaded exact evidence.  This is Experimental
green evidence only; no declaration enters `CertifiedIndex`.

## Fitting zero detectors and joint-defect fusion

For a finite module `N`, `Fitt_0(N)` cuts out `Supp(N)`.  Thus finite vanishing
gates are represented by actual coherent ideals and finite conjunctions are
fused by products.  A pure-Fitting projectivity discriminant is

```text
Delta^F_r(M)
  = Fitt_r(M) * Fitt_0(Fitt_{r-1}(M)),
```

where `Fitt_{r-1}(M)` is regarded as a finite module.  Its principal open is the
rank-`r` free locus.  This form is naturally adapted to flat base change and a
future Lean Fitting interface.

Finite cotangent, active, boundary, excess and projectivity defects can
therefore be fused into one joint-defect ideal.  The remaining apparently
infinite gate is passive normal flatness of the full graded Rees module.

## Finite Rees-Serre passive packet

For a regular centre ideal `K` and finite passive module `M`, put

```text
B = gr_K(R),
G = gr_K(M).
```

The highest-posterior new theorem asks for a finite base-change-compatible
packet consisting of bounded irrelevant torsion, finitely many low graded
pieces and the coherent sheaf on `Proj(B)`, whose flattening locus is exactly
the locus where `G` is flat over the centre.  The expected proof uses relative
Serre vanishing, cohomology and base change, and flattening stratification.

If proved, every joint-legality failure becomes finite and the support-thickness
recursion is a finite-state compiler.

## Updated decisive theorem

> **Support-Thickness Joint-Defect Ambient-Lift Alternative.**  The full finite
> bad intersection layer decomposes into singular reduced carriers and regular
> carriers with nilpotent thickness.  The former are handled by
> lower-dimensional relative resolution and passive/logarithmic ambient
> lifting; the latter by finite nilpotent-contact and Rees-Serre packets with
> strict support/thickness/contact/Hasse/Fitting descent.  The resulting clean
> arrangement admits a symmetry-compatible wonderful ordinary-centre word and
> all successor data reenter without reset.

## Remaining cut

```text
FINITE_REES_SERRE_PASSIVE_PACKET
PASSIVE_AND_LOG_SNC_AMBIENT_LIFT
NILPOTENT_CONTACT_STRICT_TRANSFORM_DESCENT
JOINT_DEFECT_MACRO_NO_RESET
```

## Truth boundary

```text
X035_EXPERIMENTAL_CLEANROOM_GREEN            = true
X035_AXIOM_AUDIT_NO_SORRYAX                  = true
X035_DECLARATIONS_PROMOTED                   = false
CERTIFIED_GRAPH_CHANGED                       = false
FINITE_REES_SERRE_PASSIVE_PACKET_PROVED      = false
PASSIVE_SNC_AMBIENT_LIFT_PROVED              = false
NILPOTENT_CONTACT_STRICT_DESCENT_PROVED      = false
UNIVERSAL_ACTUAL_CENTRE_SYNTHESIS_PROVED     = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED           = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION   = false
FORMAL_GLOBAL_STATUS                         = OPEN_GAP
```
