# MLEL-X039 / NTR-RFL

## Normal-Flatness Transitivity, Regular-Flag Lifting, and Exceptional No-Recharge

**Chinese title:** 法平坦传递、正则旗提升与例外不可再生  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X038 / PGI-ERD`  
**Primary D001 refinement:** `HER-02/HER-03 -> HER-05 -> HER-15`, with termination handoff to `TRM-03/TRM-11`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_COMPRESSION / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X038 split the ambient transform problem into two stages:

```text
A. twisted Rees base change / controlled-filtration transport;
B. purification by exceptional torsion versus associated grading.
```

The present round shows that Stage B is not an independent terminal obstacle.
If the purified associated-graded module is flat over a regular carrier, every
exceptional Cartier equation acts injectively, so the X038 defect

```text
H^0_(u)(gr_L(N / H^0_(u)(N)))
```

is zero.  One simultaneous flatification kills all such defects for all owners
and all exceptional SNC monomials.

A second, classical input supplies the hereditary mechanism.  For nested ideals
`I subset J`, with `J/I` a complete-intersection ideal in `R/I`, Hironaka's
normal-flatness comparison has the module form

```text
(gr_I(M) / J gr_I(M))
  tensor_(R/J)
  gr_(J/I)(R/I)
    ~= gr_J(M)
```

whenever `gr_I(M)` is free over `R/I`.  Thus normal flatness along a regular
carrier is transitive down every regular flag.  After one carrier has been
legalized, no later regular subcarrier needs a fresh passive-flatness charge.

The remaining project-specific bridge is the **Regular-Flag Flat-Lift
Theorem**: ambient blowup along a recursively legal flag centre must transport
the carrier's purified associated-graded portfolio exactly, with the canonical
exceptional grading twist, on every chart and overlap.

---

# 1. Exact X038 validation inherited by this round

The final X038 exact snapshot is green:

```text
PR                         = 57, draft, open, unmerged
base SHA                   = ffaf4ebb958bf40d610bc36fd6070cd407062c5b
head SHA                   = f66b99901dd3e04015a00d5fcc341cfd579d374b
merge snapshot             = ac2a567331698dabcc79e94d266747d43cd7df54
workflow run               = 30960649142
job                        = 92163618376
conclusion                 = success
Lean                       = 4.30.0
mathlib revision           = c5ea00351c28e24afc9f0f84379aa41082b1188f
artifact                   = 8912884925
artifact digest            = sha256:59dd56f02548c9c6fea14a89e84c52895066a62e04795a936f4ff01da97c41cc
```

The run built the official target and the exact X038 modules, completed the
unified axiom audit without `sorryAx`, and uploaded the exact source and report
evidence.  No declaration entered `CertifiedIndex`.

---

# 2. Flatness kills the purification--grading defect

Let `A` be a commutative ring, let `G` be an `A`-flat module, and let `u` be a
nonzerodivisor of `A`.  Tensoring

```text
0 -> A --u--> A
```

with `G` preserves injectivity, hence multiplication by `u` on `G` is
injective.  Induction gives

```text
u^n g = 0  ->  g = 0.
```

Therefore

```text
H^0_(u)(G)=0.
```

For the X038 notation

```text
T=H^0_(u)(N),
A0=gr_L(N),
H=gr_L^ind(T),
U=H^0_(u)(A0),
E=U/H,
```

one has

```text
E = H^0_(u)(gr_L(N/T)).
```

Consequently, once `gr_L(N/T)` is flat over the carrier, `E=0`.

The exact module endpoint is written in
`FlatExceptionalTorsionKill.lean` and was green in X038.  X039 packages its
hereditary interpretation in `ExceptionalNoRecharge.lean`.

---

# 3. Simultaneous SNC version

Let the exceptional boundary on a regular carrier have local equations

```text
u_1,...,u_r
```

which form part of a regular parameter system.  Every exceptional monomial

```text
u^alpha = product_i u_i^(alpha_i)
```

is a nonzerodivisor.  Hence a carrier-flat module has no nonzero submodule all
of whose sections are killed locally by powers of exceptional monomials.

Thus one simultaneous flatification of the complete purified associated-graded
portfolio gives:

```text
all owners flat over the carrier
-> no u_i-power torsion
-> no exceptional-monomial torsion
-> no purification-grading recharge after later Cartier traces.
```

The exponent vector remains a useful diagnostic and pre-flatification rank
coordinate, but it is not a new terminal obstruction after flatness.

---

# 4. Hironaka's module tensor decomposition

Let `R` be Noetherian, let

```text
I subset J subset R,
Rbar=R/I,
Jbar=J/I,
K=R/J,
```

and assume `Jbar` is a complete-intersection ideal of `Rbar`.  For a finite
`R`-module `M`, there is a natural graded Hironaka comparison

```text
Phi_(I,J,M):
  (gr_I(M) / J gr_I(M))
    tensor_K gr_Jbar(Rbar)
      -> gr_J(M).
```

A 2026 module-generalization of Hironaka's theorem proves that if `gr_I(M)` is
free as an `Rbar`-module, then `Phi_(I,J,M)` is an isomorphism.  Since
`Jbar` is a complete intersection,

```text
gr_Jbar(Rbar) ~= Sym_K(Jbar/Jbar^2),
```

which is a free `K`-module.

The module-theoretic endpoint is therefore:

```text
restriction of gr_I(M) to K is flat
+ relative normal algebra is flat
+ Hironaka comparison is an equivalence
-> gr_J(M) is flat over K.
```

This endpoint is formalized abstractly in
`HironakaTensorFlatnessCompiler.lean`.

---

# 5. Geometric transitivity corollary

Let

```text
D subset C subset X
```

be regular immersions in a locally Noetherian regular ambient scheme, and let
`M` be coherent.  Write `I=I_C` and `J=I_D`.  Locally, `J/I` is generated by a
regular sequence on `C`.

If `M` is normally flat along `C`, then each homogeneous piece of `gr_C(M)` is
locally free over `C`; in a local chart the complete graded module is free as
an `O_C`-module.  Hironaka's comparison yields

```text
gr_D(M)
  ~= gr_C(M)|_D
       tensor_(O_D)
       Sym_(O_D)(I_(D/C)/I_(D/C)^2).
```

Both factors are flat over `D`, hence `M` is normally flat along `D`.

Therefore:

> **Normal-flatness transitivity.**  Once a regular carrier is normally flat
> for the passive portfolio, every regular subcarrier in it is automatically
> normally flat for the same portfolio.

This is a standard local theorem, not a proof of the ambient lifting problem.
It becomes decisive because the wonderful and flatifier realization words are
built from nested regular carriers.

---

# 6. What transitivity does and does not solve

It solves the **post-legalization recharge problem**:

```text
C normally flat
-> every later regular D subset C normally flat
-> no new passive flatification charge down the flag.
```

It does not construct the first flatification of a raw carrier.  It also does
not by itself identify

```text
gr_(C')(M')
```

with the carrier-side strict transform of `gr_C(M)` after an ambient blowup.
That identification still requires explicit Rees/chart algebra and overlap
compatibility.

The correct algorithm therefore retains a dimension-strict preparatory macro:

```text
raw carrier C
-> choose one centre-enriched flatifier of the complete carrier portfolio
-> factor it through a regular word on C
-> recursively legalize every word centre D with dim D < dim C
-> lift D ambiently
-> use the Regular-Flag Flat-Lift Theorem
-> continue the immutable source-labelled word
-> reach a normally flat carrier
-> invoke transitivity and exceptional no-recharge thereafter.
```

No repeated same-dimensional re-flatification is allowed.

---

# 7. Regular-flag local normal form

For a regular flag `D subset C subset X`, étale-locally in a regular ring one
may choose a regular sequence

```text
I_C=(x_1,...,x_r),
I_D=(x_1,...,x_r,y_1,...,y_s).
```

In the blowup of `D`, only the `y_j`-pivot charts meet the strict transform of
`C`.  On the `y_1`-chart,

```text
x_i = y_1 x_i',
y_j = y_1 y_j'  (j>1),
I_(C')=(x_1',...,x_r').
```

Thus the controlled carrier ideal is already saturated in the regular-flag
coordinate chamber, and the old and new conormal generators differ by one
common exceptional factor.  This determines the canonical grading line twist.

The missing module theorem is to show that the complete passive Rees
filtrations obey the same exact chart relation under the recursive joint
legality certificate.

---

# 8. Candidate Regular-Flag Flat-Lift Theorem

> **Regular-Flag Flat-Lift Theorem.**  Let `D subset C subset X` be a flag of
> regular immersions in a regular Noetherian ambient scheme.  Let a finite
> passive portfolio, active marked portfolio, boundary, and source/debt ledger
> be given.  Assume `D` is jointly legal for the complete carrier Rees/normal
> portfolio attached to `C`: active powers are permissible, all relevant Rees
> exact sequences are Tor-safe, the passive and comparison modules are normally
> flat along `D`, and the flag is logarithmically transverse to the total
> boundary.  Blow up `X` in `D`, and let `C'` and `M'` denote strict transforms.
> Then on every relevant chart and overlap there is a canonical graded
> isomorphism
>
> ```text
> gr_(C')(M')
>   ~= StrictTransform_D(gr_C(M)) tensor exceptional grading twist.
> ```
>
> If the carrier-side transform is flat, then `C'` is normally flat for `M'`;
> the purification--grading defect is zero; every regular subcarrier of `C'` is
> normally flat by Hironaka transitivity; and no exceptional torsion is
> recharged.  The comparison is compatible with finite owner sums, smooth base
> change, source labels, contact packets, and boundary strata.

The coordinate ideal portion is standard.  The complete module, overlap,
source, and no-reset statement is open.

---

# 9. Revised candidate graph

```text
finite intrinsic Frobenius-Hasse/conormal state
-> finite actual raw carrier arrangement

for each raw regular carrier C:
  complete purified projective-normal/Rees portfolio
  -> one centre-enriched admissible flatifier on C
  -> lower-dimensional regular word factoring through it
  -> recursively legalize each D subset C, dim D < dim C
  -> ambient trace blowup in D
  -> Regular-Flag Flat-Lift
  -> exact carrier portfolio transport
  -> final carrier normal flatness
  -> flatness kills purification-grading torsion
  -> Hironaka transitivity down every later regular flag
  -> exceptional no-recharge

regular-support contact:
  anchor-contact ideals
  -> same dimension-strict carrier compiler
  -> residual Cartier contact cleaning

clean arrangement:
  maximal wonderful word
  -> no new passive charge on nested regular strata
  -> all-chart hereditary reentry
  -> global causal termination
  -> finite symmetry-compatible ordinary blowup word.
```

---

# 10. Exact frontier after X039

```text
X039-G1   SHEAFIFIED_HIRONAKA_COMPARISON_FOR_FINITE_OWNER_PORTFOLIOS
X039-G2   NORMAL_FLATNESS_TRANSITIVITY_ON_REGULAR_FLAGS
X039-G3   ALL_CHART_REGULAR_FLAG_CONTROLLED_IDEAL_AND_LINE_TWIST
X039-G4   TWISTED_REES_BASE_CHANGE_MAP
X039-G5   FINITE_EXCEPTIONAL_KERNEL_COKERNEL_PACKET
X039-G6   REGULAR_FLAG_FLAT_LIFT
X039-G7   CENTRE_ENRICHED_REGULAR_WORD_FACTORIZATION_OF_FLATIFIER
X039-G8   RECURSIVE_JOINT_LEGALIZATION_OF_EVERY_TRACE_SUBCENTRE
X039-G9   AMBIENT_TRACE_REALIZATION
X039-G10  FLAT_PURIFICATION_DEFECT_VANISHING_SCHEME_INTERFACE
X039-G11  EXCEPTIONAL_MONOMIAL_NO_RECHARGE
X039-G12  CARTIER_STABLE_SOURCE_COMPRESSION
X039-G13  ALL_CHART_OWNER_SOURCE_DEBT_BOUNDARY_NO_RESET
X039-G14  DIMENSION_STRICT_NESTED_LEGALIZATION
X039-G15  WONDERFUL_WORD_PASSIVE_HEREDITY
X039-G16  UNIVERSAL_ACTUAL_JOINTLY_LEGAL_CENTRE_WORD
```

The new highest-information cut is

```text
X039-G4/G5/G6
+
X039-G7/G8/G9
+
X039-G13/G14.
```

The algebraic transitivity and flat-torsion endpoint substantially compress the
passive branch, but they do not replace ambient realization or no-reset.

---

# 11. Exact Lean source written in this round

```text
HironakaTensorFlatnessCompiler.lean
ExceptionalNoRecharge.lean
NestedCarrierLegalizationRank.lean
X039NormalFlatnessTransitivityIndex.lean
X039NormalFlatnessTransitivityIndexAudit.lean
```

The slice proves only:

1. a Hironaka tensor-product equivalence transports flatness to the total
   associated graded;
2. the statement compiles simultaneously for a finite passive portfolio;
3. carrier flatness kills every submodule locally specified as exceptional
   monomial power torsion;
4. no such torsion can recharge in a successor packet;
5. recursive carrier-dimension descent dominates arbitrary later changes;
6. word-height, Rees-defect, contact, and debt drops are strict at fixed earlier
   coordinates.

It does not construct the Hironaka comparison or the geometric lifting word.

---

# 12. Annals-series maximum-likelihood estimate

The passive chapter is conceptually cleaner than X038: purification torsion is
absorbed by flatness and Hironaka transitivity replaces repeated passive checks.
The complete regular-flag and flatifier-realization proof still requires a long
all-chart chapter.  The central estimate is **558 dense
Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Anchor-Contact Ideals, Cartier-Trace Words, and Wonderful Actual-Centre Synthesis | 118 |
| III | Flat Rees Flags, Purification-Grading Interchange, and Hereditary Reentry | 138 |
| IV | Exceptional No-Recharge, Source-Debt Causality, and Dimension-Strict Termination | 86 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **558** |

A one-volume editorial edition with theorem-interface cards, the regular-flag
chart compendium, source/Cartier ledger, proof DAG, counterexample atlas, and
paper-to-Lean map is estimated at **605--642 physical pages**.

Subjective publication-form planning weights:

```text
six papers                                 0.64
seven papers, splitting regular-flag lift 0.18
five papers after consolidation            0.11
other                                      0.07
```

These are research-planning weights, not calibrated probabilities.

---

# 13. Modal decisive theorem

> **Normal-Flat Carrier Legalization and Regular-Flag Persistence Theorem.**
> Let a prepared marked state on an `n`-dimensional smooth scheme over a perfect
> field of characteristic `p>0` produce a finite symmetry-stable family of
> regular raw carriers.  Assume strong relative principalization and the same
> carrier-legalization theorem in dimensions `<n`.  Every raw carrier admits one
> centre-enriched admissible flatifier for its complete purified passive,
> Rees-comparison, logarithmic, source, and contact portfolio.  The flatifier is
> realized by a finite word of ordinary ambient blowups in regular trace
> centres, each recursively jointly legalized on a strictly
> lower-dimensional carrier.
>
> Every regular-flag edge carries a canonical all-chart, overlap-compatible
> twisted Rees comparison.  The comparison defects vanish under the joint
> legality certificate, and the associated graded of the ambient strict
> transform is the centre-enriched carrier transform.  Flatness of the final
> carrier portfolio kills all purification--grading and exceptional-monomial
> torsion.  Hironaka's tensor decomposition makes normal flatness transitive
> down every subsequent regular flag, so passive legality cannot recharge.
> Active owners, boundary strata, anchor-contact packets, sources, and debts
> reenter without reset.  Every nested call lowers carrier dimension, and every
> outer macro lowers the global causal rank.

This is the current maximum-likelihood theorem target.  It is not established.

---

# 14. Truth boundary

```text
ROUND_ID                                           = MLEL-X039 / NTR-RFL

X038_EXPERIMENTAL_CLEANROOM_GREEN                  = true
FLAT_EXCEPTIONAL_TORSION_ENDPOINT_LEAN_GREEN       = true
HIRONAKA_MODULE_COMPARISON_IDENTIFIED               = standard theorem
NORMAL_FLATNESS_TRANSITIVITY_IDENTIFIED             = true
PASSIVE_NO_RECHARGE_ARCHITECTURE_IDENTIFIED         = true
HIRONAKA_TENSOR_COMPILER_LEAN_SOURCE_WRITTEN        = true
EXCEPTIONAL_NO_RECHARGE_LEAN_SOURCE_WRITTEN         = true
NESTED_CARRIER_RANK_LEAN_SOURCE_WRITTEN             = true

SHEAFIFIED_HIRONAKA_INTERFACE_PROVED                = false
TWISTED_REES_BASE_CHANGE_MAP_PROVED                 = false
REGULAR_FLAG_FLAT_LIFT_PROVED                       = false
CENTRE_ENRICHED_FLATIFIER_REALIZATION_PROVED        = false
ALL_CHART_NO_RESET_PROVED                           = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED          = false

X039_CLEANROOM_GREEN                                = false
NEW_DECLARATIONS_PROMOTED                           = false
CERTIFIED_GRAPH_CHANGED                             = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                  = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION          = false
FORMAL_GLOBAL_STATUS                                = OPEN_GAP
```

---

# 15. Principal sources

1. A. De Stefani, J. Jeffries, N. KC, and L. Núñez-Betancourt,
   *Regularity is bounded on a quasi-excellent Noetherian scheme*, 2026,
   Proposition 2.5, a module-generalization of Hironaka's normal-flatness
   tensor decomposition.
2. H. Hironaka, *Resolution of singularities of an algebraic variety over a
   field of characteristic zero. I*, Ann. of Math. 79 (1964), Chapter II.
3. M. Herrmann and R. Schmidt, *Zur Transitivität der normalen Flachheit*,
   Invent. Math. 28 (1975), 129--136.
4. L. Robbiano, *A theorem on normal flatness*, Compos. Math. 38 (1979),
   293--298.
5. The Stacks Project, strict transforms and flatification by admissible
   blowups.
6. The current MLE--Lean baseline through X038 and the restricted
   Hasse--Morita core descent theorem.
