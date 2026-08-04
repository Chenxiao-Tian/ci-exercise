# MLEL-X033 / MWB-DFI

## Maximal Wonderful Building-Set Completion, Defect-First Intersection Profiles, and Symmetry-Safe Ordinary-Centre Serialization

**Date:** 2026-08-03/04  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parent:** `MLEL-X032 / FPP-CMS-FPA`  
**Primary D001 cut:** `G16 -> G20 -> G25 -> G26`  
**Secondary D001 cut:** `G11 -> G18 -> G26`  
**Epistemic class:** `EXPERIMENTAL_GEOMETRIC_REPAIR / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

---

## 1. Executive result

The X032 no-go theorem showed that a finite space of cardinal-minimal marked
closures need not contain a canonical symmetry-fixed point.  The present round
removes the need to choose such a point.

The central repair is:

```text
all minimal marked closures
-> all nonempty scheme-theoretic intersections
-> maximal building set
-> canonical product ideal
-> deepest/minimal strata by intrinsic rank
-> one disjoint-union ordinary centre per layer
-> finite wonderful blow-up word.
```

When every intersection stratum is regular and carries the full active,
passive, boundary and nonidentity certificates, standard wonderful-model
geometry supplies the desired symmetry-safe serialization.  The final model is
intrinsic: it is the blow-up of the product of all building-set ideals and is
independent of the admissible order used to realize it as a sequence of
ordinary smooth-centre blow-ups.

The complementary branch is defect-first:

```text
first nonregular or illegal intersection stratum
-> intrinsic configuration-difference packet
-> Jacobian/Fitting/Hasse/passive/boundary defect support
-> lower-support, contact-order or Schur-Fitting recursion.
```

The clean branch is now conceptually simple.  The remaining load-bearing
mathematics is concentrated in strict descent of the defect branch and in
hereditary transport of the project-specific marked data.

---

## 2. Why the previous single-centre strategy was unnecessary

Let `M` be the finite set of minimal acceptable correction families from X032.
For each `A in M`, let `K_A` be the corresponding closure ideal and
`C_A = V(K_A)` the centre.

X032 proved that a symmetry may exchange two distinct minimizers and that
neither intersection nor union of the two selected families is a universal
repair.  The mistake was to insist on selecting one minimizer before using the
geometry of the whole family.

The correct object is the finite intersection arrangement

```text
S(M) = { intersection of C_A over A in T |
         empty != T subset M, intersection nonempty }.
```

Because

```text
K_(A union B) = K_A sup K_B,
```

scheme-theoretic intersection is already encoded by union of correction
component sets.  Active marked containment is monotone under this operation:
if an owner ideal lies in `K_A^m`, it also lies in every larger closure ideal.
Thus every intersection stratum remains active-owner acceptable.  This does
not automatically imply passive safety, regularity, SNC compatibility or a
nonidentity action; those are retained as separate gates.

---

## 3. Clean maximal-building-set serialization theorem

### Candidate theorem MWB-01

Let `k` be a perfect field, let `X` be a regular separated finite-type
`k`-scheme, and let `E` be an ordered SNC boundary.  Let `Gamma` act on the
marked state by automorphisms.  Suppose `M` is a finite `Gamma`-stable family of
actual closed centres and let `S(M)` be the family of all nonempty
scheme-theoretic intersections.

Assume:

1. every member of `S(M)` is geometrically regular;
2. every member is active-owner marked permissible;
3. every member is passive-owner Tor-safe and normally flat in the exact sense
   required by the controlled transform;
4. every member meets `E` cleanly and the enlarged boundary remains SNC;
5. the family is stable under restriction and under the relevant smooth and
   etale base changes;
6. every layer action is nonidentity after Cartier/terminal enrollment;
7. after each layer blow-up, the transformed arrangement and all ledgers are
   reconstructed without reset.

Then:

- `S(M)` is a clean arrangement and, with the full intersection family, is its
  maximal building set;
- the product ideal

  ```text
  W(M) = product_{S in S(M)} I_S
  ```

  is intrinsic and `Gamma`-invariant;
- the wonderful model `Bl_{W(M)}(X)` is regular and its new boundary divisors
  have normal crossings;
- any admissible building-set order gives the same final model;
- ordering by intrinsic depth, equivalently by increasing dimension after
  reversing conventions, allows equal-rank minimal strata to be blown up as
  one disjoint union;
- the resulting word is a finite ordinary-centre word, not a stacky quotient
  and not an arbitrary choice of one minimizer;
- its length is bounded by the height of the finite intersection poset, and in
  particular by the number of nonempty strata.

### Evidence class

The wonderful-model implications are standard mathematical input.  The new
Lean source formalizes the finite intersection completion, active-legality
monotonicity, canonical rank-layer scheduler, permutation invariance, product
ideal invariance and the exact project-specific gate interface.  It does not
prove the scheme-level wonderful theorem or inhabit the project-specific gates.

---

## 4. The canonical product ideal is the naturality firewall

An ordinary centre word needs an order, but the final wonderful model does not.
The product

```text
W(M) = product I_S
```

has three decisive advantages:

1. it is independent of every enumeration of the building set;
2. every symmetry of the arrangement fixes it;
3. it gives one scheme-level object whose blow-up is canonically isomorphic to
   every admissible wonderful word.

Thus sequence-level tie-breaking is no longer responsible for mathematical
canonicity.  The dimension/depth scheduler is only an implementation of an
already canonical model.  This separates the global naturality problem from
the local ordinary-centre legality problem.

The Lean module `WonderfulProductIdeal` verifies the finite commutative product
invariance.  The comparison

```text
Bl_{W(M)}(X)  ~=  iterated wonderful word
```

remains a scheme-level theorem input.

---

## 5. The simple new local object: symmetric configuration differences

The deepest simplification of the round occurs on a common graph chart.
Suppose the candidate centres are graphs of sections

```text
h_a : U -> N,   a in A,
```

of one finite normal module.  Their common intersection is governed by the
condition that all sections agree.  No base minimizer should be selected.
Define instead the symmetric finite packet

```text
D(h)_(a,b) = h_a - h_b.
```

This is a linear map

```text
D : N^A -> N^(A x A).
```

Its kernel is exactly the diagonal submodule of constant families:

```text
ker(D) = image(N -> N^A).
```

The construction is equivariant under every permutation of `A`.  Therefore:

```text
multi-centre coincidence/contact
-> one intrinsic finite linear packet
-> the existing order-ideal, Fitting, Hasse and Frobenius machinery.
```

This observation suggests that the nonclean-arrangement problem is not an
independent theory.  It is a recursive instance of the same finite-packet
problem already used for the original resolution state.

### Candidate theorem SCD-02

On every compatible graph atlas, the scheme-theoretic intersection of a finite
family of regular graph centres is the zero scheme of the intrinsic
configuration-difference section.  The construction is independent of graph
frames and descends on overlaps.

### Candidate theorem SCD-03

For a nonregular difference zero scheme, either:

1. a positive-rank Hasse/Fitting direction produces a proper regular contact
   centre and lowers the contact Fitting profile; or
2. the Hasse rank is zero and Frobenius root compression lowers the degree or
   support profile; or
3. a strictly smaller defect support is exposed.

These two candidate theorems are the highest-posterior route to the defect
branch.  Their abstract linear kernel has been formalized; geometric atlas
realization and strict descent remain open.

---

## 6. Tor excess is not the clean-intersection criterion

The earlier X033 sketch used

```text
I inf J = I * J
```

as a proposed clean-intersection gate.  This is incorrect.

### Failure of necessity

For the self-pair `I = J`, the equation becomes

```text
I = I^2.
```

A non-idempotent regular Cartier ideal therefore fails the condition even
though a regular centre intersects itself cleanly.  The relation is not even
reflexive on regular centres.

### Failure of sufficiency

In `k[x,y]`, take

```text
I = (y),
J_m = (y - x^m),  m >= 2.
```

The two smooth curves are principal and relatively prime, so

```text
I intersection J_m = I * J_m.
```

Yet their scheme-theoretic intersection is

```text
Spec k[x]/(x^m),
```

which is nonreduced and nonregular.  Thus the Tor-independent equality does not
imply clean intersection.

After blowing up the origin, the `x`-chart equations become

```text
u = 0,
 u = x^(m-1),
```

so the contact length drops from `m` to `m-1`.  This model motivates an
intersection-contact rank and shows how the defect packet should interact with
existing Hasse/Frobenius descent in positive characteristic.

### Correct role of Tor

The equality remains valuable as a passive or derived-intersection diagnostic,
and comaximal/disjoint layer ideals satisfy it.  It must not replace regularity
of the scheme-theoretic intersection or the log-boundary and passive gates.

The Candidate Graph is corrected accordingly.

---

## 7. Defect-first intersection profile

For one intersection stratum `S`, the proposed intrinsic defect package has
four components.

```text
D_reg(S)   = singularity/Jacobian-Fitting defect of O_S;
D_pas(S)   = support of the passive Tor or normal-flatness defect;
D_log(S)   = degeneracy of the logarithmic conormal/boundary map;
D_act(S)   = nonidentity or remaining marked-action defect.
```

The total bad support is the canonical union of these closed supports.  On a
configuration graph atlas, `D_reg(S)` is computed from the symmetric
difference packet.

A plausible local rank is not one number but the lexicographic profile

```text
Delta(S) =
  (dimension of defect support,
   generic nilpotent/contact length,
   Hasse-rank multiset,
   Fitting-presentation multiset,
   centre-word obligation multiset).
```

The tangent-curve model strictly lowers the second coordinate.  The existing
Schur-pivot theorem lowers the presentation-size coordinate.  Existing
Frobenius-root results lower degree in the Hasse-rank-zero chamber.  What is
still missing is one geometric completeness theorem proving that every bad
stratum enters at least one of these strict modes on every chart.

This missing statement is now isolated as `X033-N6 / INTERSECTION-DEFECT-DESCENT`.

---

## 8. Correction to the Fitting-atlas expectation

The phrase

```text
finite-projective cokernel on a finite Fitting atlas covering the whole state
```

is false without a residual branch.  A finitely presented module such as
`R/(t)` over `k[t]` is not projective at `t = 0`; no open cover of the whole
base can make it locally free.

The corrected interface is:

```text
finitely presented cokernel
-> canonical projective locus, controlled by Fitting conditions
-> automatic finite dual frame and intrinsic order ideal there
-> closed nonprojective discriminant
-> Schur-Fitting residual packet on the discriminant.
```

Flattening by admissible blow-ups can provide an existence theorem for a
strict transform of a module, but it does not by itself supply regular,
marked-permissible, passive-safe centres.  Moreover, Fitting/Nash-type blow-ups
cannot be treated as a universal resolution algorithm.  They are defect
carriers inside the larger recursion.

---

## 9. Candidate Graph update

### Deleted edges

```text
cardinal-minimal family
-> canonical single centre;

I inf J = I*J
-> clean geometric intersection;

finitely presented cokernel
-> finite projective on an open cover of the whole state;

iterated Fitting/Nash blow-up
-> universal resolution.
```

### Added edges

```text
finite minimizer space
-> finite intersection arrangement;

regular jointly legal intersection arrangement
-> maximal building set;

maximal building set
-> canonical product ideal;

canonical product ideal + clean gates
-> symmetry-safe wonderful ordinary-centre word;

common graph atlas
-> symmetric configuration-difference packet;

first bad intersection stratum
-> intrinsic defect package;

intrinsic defect package
-> lower-support / contact / Hasse-root / Schur-Fitting strict descent;

finite presentation
-> projective locus + nonprojective residual discriminant.
```

---

## 10. Lean source written this round

The corrected integrated target is

```text
PCRLean.Experimental.X033WonderfulDefectIndex
```

and contains or imports:

```text
IntrinsicOrderIdealLinearEquiv
ProjectiveOrderIdealContent
SymmetricConfigurationDifference
MarkedClosureArrangement
CanonicalIntersectionCompletion
CriticalPairTorExcess
TorCleanIntersectionBoundary
SchurFittingComplexity
CanonicalLayerScheduler
WonderfulProductIdeal
WonderfulLayerSerialization
X033WonderfulDefectIndexAudit
```

The formalized content is intentionally limited to:

- finite ideal and arrangement identities;
- active-legality monotonicity;
- symmetric configuration-difference kernel;
- finite rank-layer scheduling and symmetry invariance;
- product-ideal reindexing invariance;
- Tor/clean boundary correction;
- exact conditional layer-gate compiler;
- arithmetic Schur-Fitting decrease.

No scheme-level wonderful theorem, regularity theorem, passive-safety theorem,
hereditary transform theorem or final resolution theorem is assumed.

---

## 11. Exact next theorem queue

```text
X033-N1  GRAPH-ATLAS-CONFIGURATION-DIFFERENCE-EFFECTIVITY
X033-N2  INTERSECTION-STRATUM-REGULARITY-CRITERION
X033-N3  MAXIMAL-BUILDING-SET-MARKED-LEGALITY
X033-N4  WONDERFUL-PRODUCT-BLOWUP-TO-ORDINARY-WORD
X033-N5  LAYERWISE-PASSIVE-AND-LOG-SNC-SAFETY
X033-N6  INTERSECTION-DEFECT-DESCENT
X033-N7  FITTING-DISCRIMINANT-STRICT-RESIDUAL
X033-N8  WONDERFUL-WORD-HEREDITARY-NO-RESET
X033-N9  WONDERFUL-WORD-STRICT-MACRO-RANK
X033-N10 UNIVERSAL-ACTUAL-CENTRE-WORD-CERTIFICATE
```

The next highest-posterior mission is `X033-N1 + X033-N6`: construct the
symmetric configuration-difference packet on compatible etale graph charts,
then prove the clean-or-strict-defect alternative for its zero scheme.

---

## 12. Annals-series maximum-likelihood update

This round changes the internal architecture of Papers II and IV but does not
force a seventh volume.  Wonderful completion absorbs much of the previously
separate symmetry-serialization burden, while the intersection-defect theorem
adds a substantial but already budgeted bridge.

The maximum-likelihood publication plan remains the D001 six-paper series:

| Paper | Working title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States and Finite Conormal Packets | 82 |
| II | Cokernel Obstructions, Wonderful Marked Arrangements, and Canonical Centre Words | 108 |
| III | Joint Legality and Hereditary Transform in Positive Characteristic | 116 |
| IV | Defect Carriers, Recurrent Classes, and Causal Termination | 96 |
| V | Functorial Globalization and Principalization | 74 |
| VI | Resolution of Singularities over Perfect Fields of Positive Characteristic | 44 |
|  | **Aggregate mathematical length** | **520** |

The point estimate remains 520 Annals/AMS-equivalent pages.  This is a planning
posterior, not evidence that the theorem is proved.

---

## 13. Truth boundary

```text
ROUND_ID                                         = MLEL-X033 / MWB-DFI
SYMMETRY_SAFE_CLEAN_CHAMBER_IDENTIFIED           = true
CONFIGURATION_DIFFERENCE_PACKET_WRITTEN           = true
TOR_CLEAN_FALSE_EDGE_DELETED                      = true
FITTING_WHOLE-COVER_FALSE_EDGE_DELETED            = true
LEAN_FINITE_SKELETON_WRITTEN                      = true
SCHEME_WONDERFUL_GEOMETRY_FORMALIZED              = false
PROJECT_SPECIFIC_LAYER_GATES_PROVED               = false
INTERSECTION_DEFECT_STRICT_DESCENT_PROVED         = false
WONDERFUL_WORD_HEREDITARY_NO_RESET_PROVED         = false
UNIVERSAL_ACTUAL_CENTRE_SYNTHESIS_PROVED          = false
NEW_DECLARATIONS_PROMOTED                         = false
CERTIFIED_GRAPH_CHANGED                           = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION        = false
FORMAL_GLOBAL_STATUS                              = OPEN_GAP
```

---

## References informing the mathematical design

- C. De Concini and C. Procesi, wonderful models of subspace arrangements.
- L. Li, wonderful compactification of an arrangement of subvarieties.
- R. MacPherson and C. Procesi, making conical compactifications wonderful.
- M. Raynaud and L. Gruson, flattening by blow-ups.
- The Stacks Project, Fitting ideals, flattening stratifications and flatness.
- The 2026 Annals counterexample showing that Nash blow-up is not a universal
  resolution procedure in dimension at least four.
