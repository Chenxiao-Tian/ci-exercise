# MLEL-X034 / RIC-PD-WOS

## Regular-Intersection Collapse, Projectivity Discriminants, and Wonderful Ordinary Serialization

**Chinese title:** 正则交汇坍缩、投射性判别式与奇妙普通爆破序列化  
**Date:** 2026-08-04  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parents:** `MLEL-X031`, `MLEL-X032`, `MLEL-X033`  
**Primary D001 refinement:** `G16 -> G20 -> G25 -> G26`  
**Secondary refinements:** `G11 -> G18`, `G22 -> G30`, `G45/G46`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_CORRECTION / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

---

## 0. Executive verdict

The central conclusion is a correction of the X033 geometric discriminator.

```text
Too strong:
Tor_1^R(R/I,R/J)=0
-> clean/legal critical pair.

Corrected:
regular scheme-theoretic intersection
+ regular-immersion conormal exactness
-> clean critical pair with a finite projective excess bundle,
   possibly nonzero.
```

Thus `I inf J = I*J` is the **zero-excess/transverse chamber**, not the
universal clean-intersection chamber.  Nonzero Tor excess can be completely
benign and is automatic for nested regular centres and for smooth centres with
shared normal directions.  The defect branch must start only when an
intersection ceases to be regular or quasi-regular, when its excess/conormal
object ceases to be finite projective, or when a separate active, passive, SNC,
or nonidentity gate fails.

The corrected highest-posterior edge is:

```text
finite minimizer closure arrangement
-> every nonempty scheme-theoretic intersection regular and jointly legal
-> clean arrangement with projective excess bundles
-> maximum-building-set / deepest-first wonderful ordinary blowup word

or

first nonregular / non-quasi-regular / jointly illegal stratum
-> canonical conormal, normal-cone, Fitting, owner, or boundary defect
-> Schur-Fitting / DFK-KR recursion with a separately proved strict drop.
```

This relocates the real difficulty from Tor vanishing to regularity of every
intersection stratum and strict descent on the first failing stratum.

---

## 1. Why Tor independence is not the clean-intersection condition

For ideals `I,J` in a commutative ring,

```text
Tor_1^R(R/I,R/J) ~= (I inf J)/(I*J).
```

Hence `I inf J = I*J` means zero excess.

### 1.1 Nested regular centres

In `R=k[x,y,z]`, let

```text
I=(x),   J=(x,y).
```

The corresponding smooth centres are nested and their scheme-theoretic
intersection is the smooth centre `V(J)`.  Nevertheless

```text
I inf J = I = (x),
I*J = (x^2,xy),
```

so the excess is nonzero.  More generally, for `I <= J`, Tor independence is
equivalent to the absorption identity `I=I*J`.

### 1.2 Incomparable smooth centres with a shared normal direction

In `R=k[x,y,z,w]`, let

```text
I=(x,y),   J=(x,z).
```

Both centres are smooth of codimension two, while `I+J=(x,y,z)` defines a
smooth codimension-three intersection.  The intersection is clean with excess
rank one.  But

```text
I inf J = (x,yz),
I*J = (x^2,xy,xz,yz).
```

The common equation `x` is the clean excess direction.

### 1.3 Coordinate-subspace classification

For coordinate ideals `I_A=(x_i : i in A)` and `I_B=(x_i : i in B)`, every
scheme-theoretic intersection is again a regular coordinate subspace, while

```text
I_A inf I_B = I_A*I_B  <->  A intersect B = empty,
rank(excess) = |A intersect B|.
```

Therefore Tor independence detects transversality, not general clean
intersection.

---

## 2. Atomic algebraic leaves written in Lean

### X034-A. Nested Tor no-go

`TorExcessIsZeroExcess.lean` proves:

```text
I <= J
-> TorIndependent(I,J) <-> I = I*J,
```

and consequently every nested nonabsorbed pair has nonzero excess.  The
same-centre case says Tor independence is equivalent to idempotence of the
centre ideal.

### X034-B. Split excess kernels are projective

Let `q : A -> B` be a surjective linear map.  Assume `A` and `B` are projective.
Projectivity of `B` gives a section `s : B -> A`.  The endomorphism

```text
e = id_A - s q
```

lands in `ker(q)` and restricts to the identity on `ker(q)`.  Hence `ker(q)` is
a direct summand of `A`, and therefore projective.

`SplitExcessKernel.lean` implements the projector, the kernel-valued
retraction, and the projectivity theorem.  Geometrically, this is applied to
the conormal surjection; its kernel is the clean excess bundle.

### X034-C. Prime-product edge for projectivity discriminants

For a prime ideal `P`, `ProjectivityDiscriminantPrime.lean` proves

```text
I*J <= P <-> I <= P or J <= P.
```

This is the prime-level Boolean edge needed by the projectivity discriminant.

These are local algebraic leaves only.  They do not assert the scheme-level
regular-intersection theorem or the wonderful blowup theorem.

---

## 3. Regular-Intersection Collapse: the principal theorem target

Let `X` be a regular Noetherian scheme and `{Z_a}` a finite family of closed
regular subschemes, each regularly immersed in `X`.  For nonempty `S`, write

```text
Z_S = scheme-theoretic intersection of Z_a, a in S.
```

### Candidate Theorem RIC

Assume every `Z_S` is regular.  Then:

1. each `Z_S -> X` is a regular immersion;
2. the canonical conormal map

   ```text
   direct_sum_a N^*_{Z_a/X}|_{Z_S} -> N^*_{Z_S/X}
   ```

   is surjective;
3. its kernel is finite locally free, possibly nonzero;
4. the family is a clean arrangement;
5. the excess rank is

   ```text
   sum_a codim_X(Z_a) - codim_X(Z_S);
   ```

6. the conormal and excess constructions commute with restriction, etale base
   change, and automorphisms of the arrangement.

### Proof spine

At a point of `Z_S`, let `R` be the regular local ring of `X` and let `K` be the
sum of the ideals of the participating centres.  Since `R/K` is regular, the
regular-local quotient theorem shows that `K` is generated by part of a regular
system of parameters.  Hence `Z_S -> X` is a regular immersion and `K/K^2` is
free.  The conormal map is surjective because `K` is the sum of the component
ideals.  Its source and target are finite free locally; the target is
projective, so the surjection splits and the kernel is finite projective by
X034-B.  The rank formula follows by taking ranks.

The remaining formal work is sheafification, overlap equality, etale
naturality, and exact compatibility with the finite intersection poset.

---

## 4. Wonderful ordinary serialization after regular-intersection collapse

For the X032/X033 marked closures,

```text
K_A = J + sum_{a in A} C_a,
K_A + K_B = K_(A union B).
```

Thus scheme-theoretic intersections remain inside one finite grammar.  Active
marked permissibility is monotone along these intersection closures.

### Candidate Theorem WOS

Let `X` be regular Noetherian with SNC boundary `E`.  Let `{Z_a}` be a finite,
automorphism-stable family of actual closed regular centres.  Assume every
nonempty intersection stratum:

1. is regular;
2. is active-owner marked permissible;
3. is passive-owner Tor-safe and normally flat for the passive portfolio;
4. has SNC with the total boundary;
5. defines a nonidentity action unless explicitly terminal;
6. carries certificates compatible with restriction and etale base change.

Then the maximum building set, consisting of all nonempty intersection strata,
produces a canonical deepest-first sequence of ordinary blowups.  After deeper
strata are blown up, the remaining strata in one depth layer are pairwise
disjoint, so their disjoint union is one regular automorphism-invariant ordinary
centre.  The resulting word:

- uses no minimizer selector;
- is invariant under automorphisms of the arrangement;
- is independent of ordering inside a layer;
- consists of actual coherent ordinary centres;
- preserves the supplied active/passive/SNC certificates; and
- separates the strict transforms of the original minimizer centres.

The classical wonderful-model theorem supplies the geometric blueprint, but
the project still needs the exact scheme-level marked-owner, passive, boundary,
and hereditary version.

---

## 5. The genuine first-defect branch

A failed intersection stratum must be selected canonically from the finite
intersection poset and its symmetry orbits.  The failures are typed.

### 5.1 Regularity/projectivity defect

For the stratum ideal `K_S`, the conormal module

```text
C_S = K_S / K_S^2
```

must be finite locally free.  Its nonprojective locus is detected by Fitting
and annihilator data.

### 5.2 Quasi-regular/normal-cone defect

A regular quotient is not a substitute for a regular immersion.  One must
control

```text
Sym_{O_{Z_S}}(C_S) -> gr_{K_S}(O_X).
```

Failure is a normal-cone defect belonging to `FND-13/CTR-09`.

### 5.3 Joint-legality defects

Even a regular clean stratum may fail active marked containment, passive safety,
normal flatness, boundary SNC, or nonidentity.  These are independent gates;
centre-centre excess must not be confused with passive-owner Tor safety.

### 5.4 Strict recursion obligation

The open edge is:

```text
finite presentation of the first failing conormal/normal-cone/owner module
-> projectivity discriminant and determinant charts
-> positive pivot: Schur residual with smaller presentation shape
-> zero/degenerate pivot: DFK-KR or rank-zero branch
-> strict decrease of support/Fitting/kernel profile on every successor.
```

Only the positive Schur arithmetic and restricted kernel-regularization
chambers are currently available.  The universal strict geometric drop remains
open.

---

## 6. Projectivity discriminant

Let `R` be Noetherian and `M` finitely presented.  Put

```text
F_r = Fitt_r(M),   F_{-1}=0,
Delta_r(M) = F_r * Ann(F_{r-1}).
```

For a prime `p`, the Fitting criterion gives

```text
M_p free of rank r
<-> (F_{r-1})_p=0 and (F_r)_p=R_p.
```

Finite generation of `F_{r-1}` gives

```text
(F_{r-1})_p=0
<-> Ann(F_{r-1}) is not contained in p.
```

The prime-product theorem gives

```text
Delta_r(M) not contained in p
<-> F_r not contained in p
    and Ann(F_{r-1}) not contained in p.
```

Therefore the proposed exact point-locus theorem is

```text
D(Delta_r(M))
= {p | M_p is free of rank r}.
```

If `M` is generated by `n` elements, define

```text
Delta_proj(M) = sum_{r=0}^n Delta_r(M).
```

Then

```text
D(Delta_proj(M))
= {p | M_p is finite projective}.
```

This is a theorem about the underlying open locus; it is not a replacement for
the standard scheme-theoretic Fitting strata.  The full Fitting-annihilator
statement is the next Lean node.

---

## 7. Machine falsification

A bounded monomial/combinatorial checker executed `3,891,557` cases with zero
failures:

| Check | Cases | Failures |
|---|---:|---:|
| Coordinate clean intersections: Tor-independent iff zero excess | 87,380 | 0 |
| Nested nonzero coordinate centres have Tor excess | 9,330 | 0 |
| Coordinate excess-rank formula | 1,398,100 | 0 |
| Prime product-containment law | 2,396,744 | 0 |
| Three-axis strict-transform chart correction | 3 | 0 |

The computation rejects the false Tor gate and checks the local formulas.  It
is not a universal proof.

---

## 8. Candidate Graph update

Deleted or redirected:

```text
Tor_1(R/I,R/J)=0 <-> clean critical pair.
```

Retained:

```text
Tor_1(R/I,R/J)=0 <-> zero-excess/transverse critical pair.
```

New principal edge:

```text
all intersection strata regular immersions
-> finite-projective conormal excess kernels
-> clean arrangement
-> wonderful ordinary serialization.
```

New defect edge:

```text
first nonregular/non-quasi-regular/jointly-illegal stratum
-> canonical projectivity/normal-cone/owner defect carrier
-> strict Schur-Fitting/DFK-KR recursion.
```

Updated critical path:

```text
FND-11 projectivity discriminant/order ideal
-> CTR-05 regular-intersection/Fitting stratification
-> CTR-07 minimizer arrangement without selector
-> CTR-12 wonderful word or first-defect recursion
-> CTR-13 universal actual-centre synthesis
-> HER-05 joint legality
-> HER-15 all-chart no-reset
-> TRM-04/05/06 support/Fitting/SCC descent
-> TRM-12 local termination
-> GLB-04/07 global serialization
-> FIN-01/04.
```

---

## 9. Exact open frontier

```text
X034-G1  SCHEME_LEVEL_REGULAR_INTERSECTION_COLLAPSE
X034-G2  EXCESS_BUNDLE_BASE_CHANGE_AND_OVERLAP_NATURALITY
X034-G3  FULL_PROJECTIVITY_DISCRIMINANT_THEOREM_IN_LEAN
X034-G4  FINITE_INTERSECTION_STRATUM_EXTRACTION_FROM_MINIMIZERS
X034-G5  WONDERFUL_SERIALIZATION_WITH_ACTIVE_PASSIVE_SNC_CERTIFICATES
X034-G6  FIRST_NONREGULAR_STRATUM_CANONICAL_DEFECT_CARRIER
X034-G7  NORMAL_CONE_DEFECT_FINITE_PACKETIZATION
X034-G8  SCHUR_FITTING_DFK_KR_STRICT_GEOMETRIC_DESCENT
X034-G9  TRANSFORMED_PACKET_NO_LATTICE_EXTERNAL_BIRTH
X034-G10 HEREDITARY_REENTRY_OF_INTERSECTION_AND_EXCESS_DATA
X034-G11 SYMMETRY_COMPATIBLE_GLOBAL_LAYER_SERIALIZATION
X034-G12 COMPOSITE_SUPPORT_FITTING_EXCESS_SCC_RANK
```

The next highest-information cut is `X034-G1 + X034-G3`.  Once these are closed,
the geometry splits cleanly into a wonderful branch and a genuine first-defect
branch.

---

## 10. Lean and clean-room state

Exact source branch:

```text
pcr-fractal-x034-ric-pd-wos-base-20260804
```

Written source:

```text
TorExcessIsZeroExcess.lean
SplitExcessKernel.lean
ProjectivityDiscriminantPrime.lean
X034RegularIntersectionIndex.lean
X034RegularIntersectionIndexAudit.lean
```

The dedicated workflow rejects `axiom`, `sorry`, and `admit`, builds the
official target, elaborates the integrated source, runs `#print axioms`, rejects
`sorryAx`, snapshots exact sources and records SHA-256 checksums.  At this
record snapshot the draft PR has not yet supplied green evidence.

```text
STATEMENTS_WRITTEN       = true
BASE_BRANCH_FROZEN       = true
CLEANROOM_GREEN          = false
PROMOTED                 = false
```

---

## 11. Updated maximum-likelihood Annals series

The highest-posterior final form remains a six-paper series.  The central
estimate is revised to **550 dense Annals/AMS-equivalent pages**:

| Paper | Updated title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 88 |
| II | Order-Ideal Content, Regular-Intersection Arrangements, and Wonderful Actual-Centre Synthesis | 114 |
| III | Joint Legality, All-Chart Transforms, and Hereditary Reentry without Reset | 120 |
| IV | Fitting Defects, Recurrent Classes, and Causal Termination | 102 |
| V | Global Descent, Symmetry-Compatible Wonderful Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **550** |

The decisive unresolved theorem is the local dichotomy:

```text
all minimizer intersection strata regular and jointly legal
-> wonderful ordinary serialization

or

first failing stratum
-> canonical finite defect packet with strict geometric descent.
```

---

## 12. Truth boundary

```text
TOR_GATE_CORRECTED                               = true
SPLIT_EXCESS_KERNEL_THEOREM_WRITTEN              = true
PRIME_PRODUCT_DISCRIMINANT_EDGE_WRITTEN          = true
REGULAR_INTERSECTION_COLLAPSE_PROVED             = false
WONDERFUL_SERIALIZATION_PROVED                   = false
FIRST_DEFECT_STRICT_DROP_PROVED                  = false
CLEANROOM_GREEN                                  = false
NEW_DECLARATIONS_PROMOTED                        = false
CERTIFIED_GRAPH_CHANGED                          = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED               = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION       = false
FORMAL_GLOBAL_STATUS                             = OPEN_GAP
```
