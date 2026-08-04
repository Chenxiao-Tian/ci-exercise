# MLEL-X035 / STD-ALI - CI and Joint-Defect Supplement

**Date:** 2026-08-04  
**Class:** `EXPERIMENTAL_GREEN_SLICE + CANDIDATE_GRAPH_SUPPLEMENT`  
**Global status:** `OPEN_GAP`  
**Theorem promotion:** none

## 1. Exact clean-room result

The repaired exact-snapshot workflow completed successfully:

```text
PR                                  = #45
base                                = pcr-fractal-x035-std-ali-base-20260804
head                                = pcr-fractal-x035-std-ali-head-20260804
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

The run:

1. rejected `axiom`, `sorry`, and `admit` in the X035 slice;
2. bootstrapped and hashed the exact Lake manifest;
3. completed the official default build (`8539` jobs);
4. built every new module through Lake module targets;
5. built the integrated X035 index;
6. ran the unified `#print axioms` audit and found no `sorryAx`;
7. uploaded exact source, environment, elaboration, audit, and checksum evidence.

The declarations use only the standard Lean foundations reported by the audit
(`propext`, `Quot.sound`, and where finite-set classical reasoning is used,
`Classical.choice`).  This is a successful Experimental clean-room result, not
promotion into `CertifiedIndex` and not proof of any scheme-level bridge.

## 2. Additional simplification: Fitting zero detectors

For a finite module `N`, the ideal

```text
zeta(N) = Fitt_0(N)
```

cuts out its support.  Therefore

```text
p in D(zeta(N))  <->  N_p = 0.
```

This is the canonical finite language for every gate whose content is the
vanishing of a finitely presented obstruction module.  Finite conjunctions are
fused by products because

```text
Fitt_0(N_1 directSum ... directSum N_s)
  = product_i Fitt_0(N_i).
```

The projectivity discriminant can therefore be made purely Fitting-theoretic.
For

```text
F_r = Fitt_r(M),
Z_r = Fitt_0(F_{r-1})          -- F_{r-1} regarded as a finite module,
Delta^F_r(M) = F_r * Z_r,
```

one has

```text
D(Delta^F_r(M)) = {p | M_p is free of rank r}.
```

Unlike the annihilator formula, this version is naturally aligned with flat
base change and with a future Lean Fitting interface.

## 3. Cotangent-Fitting defect carrier

For a finite-presentation algebra `A/k`, the smoothness defect is represented
by a finite cotangent presentation.  In the maximum-likelihood formulation,
let

```text
T_A     = H^{-1}(tau_{[-1,0]} L_{A/k}),
Omega_A = Omega_{A/k}.
```

The candidate discriminant

```text
Theta^F_{A/k}
  = Fitt_0(T_A) * Pi^F(Omega_A)
```

has open complement equal to the smooth locus; over a perfect field this is the
regular locus.  Pulling it back from a bad intersection stratum produces an
intrinsic finite-type carrier of the singular reduced-support branch.

The exact cotangent-complex truncation, sheafification, and flat-base-change
interfaces remain separate theorem obligations; this supplement does not
classify them as Lean-closed.

## 4. Finite joint-defect fusion

For one candidate stratum, all finite gates can be collected into one packet:

```text
geometric:
  cotangent regularity, quasi-regularity, conormal excess projectivity;
active:
  (I_owner + K^m)/K^m;
boundary:
  regularity and excess packets for every finite boundary stratum;
projective:
  projectivity discriminants for finite conormal/Fitting modules;
action:
  zero/unit/Cartier/nonidentity classification.
```

Their Fitting ideals multiply to one actual coherent joint discriminant.  Its
principal open is exactly the locus where all finite gates hold.

The remaining apparently infinite gate is passive normal flatness, because it
requires flatness of the full graded Rees module rather than one finite graded
piece.

## 5. Highest-posterior new theorem: finite Rees-Serre passive packet

Let `K` define a regular centre, let

```text
B = gr_K(R) ~= Sym_{R/K}(K/K^2),
G = gr_K(M)
```

for a finite passive module `M`.  The proposed theorem is:

> **Finite Rees-Serre Passive Packet.**  From a finite graded presentation of
> `G`, construct a base-change-compatible integer `N`, the bounded irrelevant
> torsion module, the pieces `G_0,...,G_N`, and the coherent sheaf `G~` on
> `Proj(B)`, such that `G` is flat over the centre if and only if this finite
> packet lies in its flattening locus.

The proof is expected to combine bounded graded torsion, relative Serre
vanishing, eventual comparison of graded pieces with projective global
sections, cohomology and base change, and flattening stratification.

If established, passive normal flatness becomes a finite Fitting/flattening
packet.  Then every joint-legality failure is carried by one finite coherent
joint-defect ideal, and the X035 support-thickness recursion becomes entirely
finite-state.

## 6. Updated decisive local theorem

The strongest current maximum-likelihood local theorem is:

> **Support-Thickness Joint-Defect Ambient-Lift Alternative.**  For the finite
> minimizer-intersection arrangement of a prepared marked state, construct the
> full choice-free bad layer and its finite joint-defect packets.  Singular
> reduced carriers are processed by lower-dimensional relative resolution and
> passive/logarithmic ambient lifting.  Regular reduced carriers carry finite
> nilpotent-contact and Rees-Serre packets whose
> support/thickness/contact/Hasse/Fitting profile strictly decreases.  After
> finitely many macros all strata are regular and jointly legal, and the maximal
> building set admits a symmetry-compatible wonderful word of ordinary
> blowups.  All successor packets and ledgers reenter without reset.

## 7. Exact remaining load-bearing cut

```text
X035-CUT-A  FINITE_REES_SERRE_PASSIVE_PACKET
X035-CUT-B  PASSIVE_AND_LOG_SNC_AMBIENT_LIFT
X035-CUT-C  NILPOTENT_CONTACT_STRICT_TRANSFORM_DESCENT
X035-CUT-D  JOINT_DEFECT_MACRO_NO_RESET
```

The finite combinatorial and ideal-power leaves are clean-room green.  The four
geometric edges above are not proved.

## 8. Truth boundary

```text
X035_EXPERIMENTAL_CLEANROOM_GREEN            = true
X035_AXIOM_AUDIT_NO_SORRYAX                  = true
X035_DECLARATIONS_PROMOTED                    = false
CERTIFIED_GRAPH_CHANGED                       = false
FINITE_REES_SERRE_PASSIVE_PACKET_PROVED      = false
PASSIVE_SNC_AMBIENT_LIFT_PROVED              = false
NILPOTENT_CONTACT_STRICT_DESCENT_PROVED      = false
UNIVERSAL_ACTUAL_CENTRE_SYNTHESIS_PROVED     = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED           = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION   = false
FORMAL_GLOBAL_STATUS                         = OPEN_GAP
```
