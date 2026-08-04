# MLEL-X033 / MAWS-TED

## Minimizer Arrangements, Wonderful Serialization, and Tor-Excess Defect

**Chinese title:** 极小中心排列、奇妙序列化与 Tor 过剩缺陷  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parents:** `MLEL-X031 / ACI-MMR-OIH`, `MLEL-X032 / FPP-CMS-FPA`  
**Primary D001 refinement:** `G16 -> G20 -> G25 -> G26`  
**Secondary correction:** `G11 -> G18`  
**Class:** `EXPERIMENTAL_REFINEMENT / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

## 1. Load-bearing cut selected

X032 proved that cardinal-minimal marked correction families need not admit a
symmetry-fixed single selector.  The correct next question is therefore not
"which minimizer should be chosen?" but:

```text
How can the entire finite minimizer space be compiled into a canonical finite
word of ordinary legal blowups?
```

The present round attacks precisely D001 `CTR-07`, `CTR-12`, and the edge into
`CTR-13`.  At the same time it red-teams the X032 phrase "finite-projective
cokernel on a finite Fitting atlas" and replaces the false global-cover reading
by a projective-locus / defect-locus recursion.

## 2. First structural simplification: minimizers form an intersection
arrangement

For a base order ideal `J`, finite correction ideals `C_a`, and a selected
family `A`, write

```text
K_A = J + sum_{a in A} C_a.
```

For two selected families `A,B`, the corresponding closed centres satisfy

```text
V(K_A) intersect V(K_B) = V(K_A + K_B)
                            = V(K_(A union B)).
```

Thus the pairwise intersection is not a new arbitrary object: it is another
closure in the same finite grammar.  More generally, every finite intersection
of minimizer centres is indexed by the union of the underlying correction
families.

The active marked condition is monotone.  If

```text
D_o <= K_A^(m_o)
```

for every active owner, then `K_A <= K_(A union B)` implies

```text
D_o <= K_(A union B)^(m_o).
```

Hence **every intersection stratum of the minimizer arrangement is
active-owner acceptable**.  This is the first exact positive replacement for
an arbitrary symmetry-breaking selector.

The Lean file `MarkedClosureArrangement.lean` proves closure monotonicity,
active acceptability monotonicity, the exact identity

```text
K_(A union B) = K_A sup K_B,
```

and a choice-free same/disjoint/intersecting pair classifier.

## 3. The previous `(2)+(3)=(1)` counterexample changes meaning

X032 used the integer ideals `(2)` and `(3)` to show that summing two proper
minimal defect ideals can give the unit ideal.  This still blocks replacement
of two minimizers by one proper centre.  But for serialization it has the
opposite, favourable meaning:

```text
K_A + K_B = R
<-> V(K_A) intersect V(K_B) is empty.
```

So the unit-intersection branch is not a dead end.  It is the **disjoint
critical-pair chamber**, where the two ordinary blowups commute and no tie
breaking is geometrically necessary.

The exact first critical-pair split is therefore

```text
same centre
or
comaximal/disjoint centres
or
proper scheme-theoretic intersection.
```

## 4. Tor-excess is the next obstruction, not arbitrary ordering

For two centre ideals `I,J`, set the elementary Tor-independence predicate

```text
I intersect J = I*J.
```

For commutative rings this is the ideal criterion corresponding to

```text
Tor_1^R(R/I, R/J) = 0.
```

The source `CriticalPairTorExcess.lean` isolates this symmetric condition and
its exact independent/excess split.  It deliberately proves no blowup
commutation theorem.

The proposed geometric discriminator is the excess module

```text
E(I,J) = (I intersect J)/(I*J).
```

The clean chamber should be characterized by regularity of the intersection
and finite local freeness of the appropriate excess/conormal data.  The
nonclean chamber is carried by the Fitting nonprojectivity locus of `E(I,J)`.
This turns a failed critical pair into an actual finite module defect rather
than an arbitrary choice problem.

## 5. Conditional wonderful-serialization theorem

The strongest retained candidate theorem is the following.

### MAWS theorem, conditional form

Let `X` be regular Noetherian with SNC boundary `E`.  Let `{Z_a}` be a finite,
symmetry-stable family of actual closed regular centres.  Assume:

1. every nonempty scheme-theoretic intersection `Z_S` is regular;
2. the family is closed under intersections and all intersections are clean;
3. every `Z_S` is active marked-permissible;
4. every `Z_S` is passive Tor-safe and normally flat for the full passive
   portfolio;
5. every `Z_S` has SNC with the total boundary;
6. every centre action is nonidentity unless it is explicitly classified as
   terminal enrollment.

Then there exists a canonical finite sequence of ordinary blowups obtained by
blowing the deepest intersection strata first.  After all deeper strata have
been blown up, the strict transforms in one layer are pairwise disjoint; their
disjoint union is one regular symmetry-invariant ordinary centre.  Blowing the
layers gives a finite sequence which:

- is equivariant under automorphisms of the arrangement;
- uses no arbitrary minimizer selector;
- is independent of ordering inside each layer;
- preserves all active/passive/boundary gates by the supplied stratum
  certificates; and
- separates the strict transforms of the original minimizer centres.

This is the maximum-building-set/wonderful-model route, rewritten for ordinary
centre words with marked owners and boundaries.

### Exact missing edge

The present round does **not** prove that minimizer centres always satisfy the
six arrangement hypotheses.  The missing theorem is a finite dichotomy:

```text
all intersection strata are jointly legal and clean
-> wonderful serialization

or
some first failing stratum has a canonical Tor/Fitting/conormal defect carrier
with strictly smaller support/Fitting complexity.
```

That dichotomy is now the corrected load-bearing edge into `CTR-12/CTR-13`.

## 6. Secondary architecture correction: projectivity is a locus, not an
atlas covering every point

For a finitely presented module `M`, it is false in general that an open cover
of the whole base makes `M` finite projective.  The basic counterexample is

```text
R = k[t],  M = R/(t).
```

On `D(t)`, `M` is zero and hence free of rank zero.  At the prime `(t)`, the
localized module is nonzero torsion over a local domain and is not free.  Thus
no projective open atlas covers the whole spectrum.

Over a Noetherian ring, write `F_r = Fitt_r(M)` and `F_{-1}=0`.  Define

```text
Delta_r(M) = F_r * Ann(F_{r-1}),
Delta_proj(M) = sum_r Delta_r(M).
```

The exact proposed theorem is

```text
D(Delta_r(M))
 = {p | M_p is free of rank r},

D(Delta_proj(M))
 = {p | M_p is finite projective}.
```

The proof combines the Fitting criterion

```text
M_p free rank r
<-> Fitt_{r-1}(M)_p = 0 and Fitt_r(M)_p = R_p
```

with finite generation of `Fitt_{r-1}`:

```text
I_p = 0 <-> Ann(I) is not contained in p.
```

Accordingly, X032-N1 is corrected to

```text
finitely presented cokernel packet
-> canonical projectivity discriminant
-> projective locus: intrinsic order/content-ideal compiler
-> defect locus: Schur-Fitting residual packet and strict recursion.
```

## 7. Schur-Fitting residual recursion

On a determinant chart with an invertible `r x r` pivot block,

```text
M = [A B; C D],    det(A) invertible,
```

block row and column operations give

```text
L*M*R = [I_r 0; 0 S],
S = D - C*A^{-1}*B.
```

For an affine target `b=(b_1,b_2)`, the residual obstruction is

```text
b_res = b_2 - C*A^{-1}*b_1.
```

Hence the localized cokernel/obstruction problem reduces to the Schur residual
packet `(S,b_res)`.  If `S=0`, the cokernel is free and the intrinsic order
ideal is generated by residual coordinates.  If `S != 0` and `r>0`, the
presentation shape decreases from `(m,n)` to `(m-r,n-r)`.  The Lean file
`SchurFittingComplexity.lean` proves strict decrease of `m+n` and
well-foundedness of the positive-pivot recursion.  The actual Schur cokernel
equivalence and the rank-zero geometric exit remain open leaves.

## 8. Candidate-graph update

Deleted or weakened edges:

```text
cardinal-minimal family -> canonical single centre

finite Fitting atlas -> projective cokernel everywhere
```

Retained replacement:

```text
finite minimizer space
-> intersection semilattice
-> same/disjoint/proper-intersection coverage
-> clean legal arrangement -> layerwise wonderful word
-> Tor/Fitting excess -> lower-support residual task

finitely presented cokernel
-> projectivity discriminant
-> projective order/content branch
-> Schur-Fitting defect recursion.
```

## 9. New exact frontier

```text
X033-N1  PROJECTIVITY_DISCRIMINANT_SCHEME_THEOREM
X033-N2  INTRINSIC_ORDER_IDEAL_AS_CONTENT_IDEAL
X033-N3  FRAME_FREE_FINITE_PROJECTIVE_BASE_CHANGE
X033-N4  SCHUR_COKERNEL_AND_OBSTRUCTION_EQUIVALENCE
X033-N5  RESIDUAL_PACKET_PRESENTATION_INDEPENDENCE
X033-N6  MINIMIZER_INTERSECTION_LATTICE_FINITE_SHEAFIFICATION
X033-N7  CLEAN_ARRANGEMENT_RECOGNITION_FROM_TOR_EXCESS
X033-N8  JOINT_LEGALITY_OF_ALL_INTERSECTION_STRATA
X033-N9  LAYERWISE_WONDERFUL_ORDINARY_BLOWUP_THEOREM
X033-N10 NONCLEAN_FITTING_DEFECT_STRICT_SUPPORT_DROP
X033-N11 WONDERFUL_WORD_HEREDITARY_NO_RESET
X033-N12 MACRO_RANK_DECREASE_AFTER_SERIALIZATION
```

## 10. Lean evidence produced

The exact source slice contains:

- `IntrinsicOrderIdealLinearEquiv.lean`;
- `MarkedClosureArrangement.lean`;
- `CriticalPairTorExcess.lean`;
- `SchurFittingComplexity.lean`;
- `X033MinimizerArrangementIndex.lean`;
- `X033MinimizerArrangementIndexAudit.lean`.

The source claims only the algebraic leaves listed above.  It does not hide
regularity, clean intersection, passive safety, SNC, blowup commutation, or
strict global descent inside a typeclass.

## 11. Truth boundary

```text
MINIMIZER_INTERSECTION_ALGEBRA_WRITTEN          = true
ACTIVE_ACCEPTABILITY_MONOTONICITY_WRITTEN       = true
ORDER_IDEAL_LINEAR_EQUIV_INVARIANCE_WRITTEN     = true
TOR_EXCESS_CASE_SPLIT_WRITTEN                   = true
SCHUR_SHAPE_STRICT_DESCENT_WRITTEN              = true
PROJECTIVITY_ATLAS_OVERCLAIM_CORRECTED          = true
WONDERFUL_SERIALIZATION_MATHEMATICALLY_COMPLETE = false
ALL_INTERSECTION_STRATA_JOINTLY_LEGAL_PROVED    = false
NONCLEAN_DEFECT_STRICT_DROP_PROVED              = false
NEW_CLEANROOM_GREEN                             = false
NEW_DECLARATIONS_PROMOTED                       = false
CERTIFIED_GRAPH_CHANGED                         = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED              = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION      = false
FORMAL_GLOBAL_STATUS                            = OPEN_GAP
```
