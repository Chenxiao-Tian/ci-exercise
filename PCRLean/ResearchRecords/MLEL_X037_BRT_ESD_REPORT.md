# MLEL-X037 / BRT-ESD

## Bi-Rees Transport, Exceptional Saturation Debt, and Ambient Flatifier Realization

**Chinese title:** 双 Rees 运输、例外饱和债务与环境平坦化实现  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parents:** `MLEL-X035 / STD-ALI`, `MLEL-X036 / PNF-ACL`  
**Primary refinement:** `G26 -> G29 -> G31 -> G41 -> G52/G53`, with a new weighted-ambient return edge to `G61`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_REWRITE / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X036 proposed that one should flatify the projective-normal packet on a raw
regular candidate centre and lift the same modification to the ambient scheme.
The present round finds a decisive obstruction to that naive edge.

Ordinary strict transform on the carrier removes all exceptional-power torsion
at once.  One ordinary ambient blowup generally removes only a positive
**controlled exceptional layer**.  Therefore

```text
flat strict-transform target on the carrier
!=
actual projective-normal packet after one ambient lift.
```

The difference is not an error term that can be ignored.  It is the contact
phenomenon itself.  The correct replacement is

```text
actual ambient packet
-> exceptional saturation
-> flat strict-transform target,
```

with a finite coherent exceptional-torsion discrepancy between the first two
objects.  Its nilpotence/contact profile is the **exceptional saturation debt**.

The new maximum-likelihood macro is

```text
projective-normal packet
-> proper flatification of its strict-transform target
-> bi-Rees comparison with the actual ambient packet
-> finite exceptional saturation debt
-> weighted ambient flatifier
-> ordinary regular toroidal word dominating the weighted modification
-> actual passive-normal-flat and contact-clean packet.
```

This unifies passive normal flatness, regular-support contact cleaning, and a
large part of logarithmic boundary legalization.

---

# 1. The counterexample that rejects the naive X036 transport edge

Let

```text
R = k[u,x],
X = Spec(R),
C = V(x),
D = V(u,x) subset C.
```

The carrier `C` is a regular curve and `D` is the effective Cartier divisor
`u=0` on `C`.  Thus the blowup of `C` in `D` is the identity morphism.

For `m>=2`, let

```text
Y_m = V(x-u^m).
```

As a `k[u]`-module, `O_{Y_m}=k[u]`, and multiplication by the normal coordinate
`x` is multiplication by `u^m`.  Hence

```text
gr_(x)(O_{Y_m}) ~= (k[u]/(u^m))[T].
```

The associated coherent sheaf on the rank-one projectivized normal bundle is
therefore

```text
F_m = O_C/(u^m).
```

Because the carrier blowup is the identity with exceptional divisor `D`, the
ordinary strict transform of `F_m` is zero: every section is supported on `D`.

Now blow up the ambient plane in `D`.  On the `u`-chart write

```text
x = u t.
```

Then

```text
x-u^m = u(t-u^(m-1)),
```

so the ambient strict transform is

```text
t-u^(m-1)=0.
```

Along the strict transform `C'=V(t)`, the new projective-normal packet is

```text
F'_m = O_C/(u^(m-1)),
```

not zero.  Consequently

```text
F'_m != strictTransform_D(F_m).
```

The carrier strict transform has removed all `D`-torsion, while the ambient
blowup has consumed exactly one contact layer.

This example is the new mandatory counterexample for every proposed passive
flatification theorem.

---

# 2. Weighted graph charts reveal the correct scalar law

The same calculation with

```text
x^q-u^m
```

gives, on the chart `x=ut`,

```text
u^q t^q-u^m.
```

If `q<=m`, then

```text
u^q t^q-u^m
  = u^q (t^q-u^(m-q)),
```

and the residual debt is

```text
m -> m-q.
```

If `m<q`, then

```text
u^q t^q-u^m
  = u^m (u^(q-m)t^q-1),
```

whose restriction to the carrier chart has unit constant term; the contact
branch is terminal there.

Thus one blowup carries a positive finite **exceptional charge** `q`.  The exact
factorizations and strict numerical drop are formalized in
`WeightedContactCleaning.lean`.

---

# 3. Strict target, actual packet, and saturation discrepancy

Let `C -> X` be a regular immersion with ideal `I`, let `D -> C` be a regular
subcentre, and let

```text
b_X : X^+ -> X,
b_C : C^+ = Bl_D(C) -> C
```

be the ambient blowup and the induced strict-transform morphism.  Write `E` for
the exceptional divisor on `C^+`.

For a coherent owner `M`, define its projective-normal packet

```text
PN_C(M)
  = tilde(gr_I(M))
```

on the projectivized normal bundle `P_C(N_{C/X})`.

Nested regular coordinates give

```text
N_{C^+/X^+}
  ~= b_C^* N_{C/X} tensor O_{C^+}(-E).
```

Projectivization is unchanged by a line-bundle twist, so the old and new
projectivized normal bundles are canonically compared after base change.

There are then two distinct transforms:

```text
STRICT TARGET
F^str = strict transform of PN_C(M) over b_C;

ACTUAL PACKET
F^act = PN_{C^+}(M^+),
```

where `M^+` is the actual ambient strict/controlled transform.

The decisive X037 theorem target is not equality of these two objects.  It is
the **saturation comparison**

```text
F^act / H^0_E(F^act)
  ~= F^str tensor (an invertible normal-line twist).
```

Equivalently, after canonical regrading, the kernel and cokernel of the bi-Rees
comparison are coherent `E`-power torsion.

The tangent graph above satisfies this exactly:

```text
F^act = O/(u^(m-1)),
H^0_E(F^act)=F^act,
F^str=0.
```

---

# 4. The bi-Rees object

Let `I subset J` be the nested ideals of `C` and `D`.  The actual transport is
governed by the two filtrations simultaneously.  The candidate algebraic
carrier is a finitely generated bi-Rees module built from

```text
{ I^a J^b M }_(a,b>=0)
```

together with the exceptional saturation required by ordinary strict
transform.  On an adapted chart with exceptional equation `u`, normal
coordinates satisfy

```text
x_i = u t_i.
```

The `I`-degree records normal order, while the `J`-degree records exceptional
charge.  Regrading along the chart diagonal produces the new normal filtration.
The failure of the two procedures

```text
first take gr_I, then strict-transform over J/I

and

first ambient-transform M, then take gr_(I^+)
```

to agree before saturation is precisely the exceptional discrepancy.

The proposed **Bi-Rees Saturation Comparison Theorem** must prove:

1. finite presentation of the comparison map;
2. equality away from the exceptional divisor;
3. exceptional-power torsion kernel and cokernel;
4. compatibility with standard charts and overlaps;
5. normal-line regrading under `N_{C^+/X^+}`;
6. flat and smooth base change;
7. composition under a finite carrier word.

No version of this theorem is claimed proved in this round.

---

# 5. Exceptional saturation debt

Let `F` be one actual packet after the carrier flatification word and let

```text
T_E(F) = H^0_E(F)
```

be its exceptional-power torsion.  Since `F` is coherent on a Noetherian
quasi-compact space and `T_E(F)` is supported on `E`, some finite power of the
invertible ideal `I_E` annihilates it:

```text
I_E^N T_E(F) = 0.
```

Define the saturation debt

```text
sigma_E(F)
  = min { N : I_E^N T_E(F)=0 }.
```

For a finite owner/contact/boundary portfolio, retain the complete finite
multiset of source-labelled debts rather than a scalar maximum.  Source labels
are immutable and exceptional divisors are aged exactly as in the existing
no-recharge ledger.

The strict target is obtained after all these debts are consumed.  In local
Cartier coordinates this is elementary linear algebra: if `T` is multiplication
by the exceptional equation, then

```text
range(T^q) ~= M / ker(T^q).
```

If `ker(T^N)` is the complete exceptional torsion, then

```text
range(T^N) ~= M / T_E(M),
```

up to the invertible `I_E^N` twist.  This exact quotient-range compiler is
formalized in `ExceptionalLayerTransform.lean`.

---

# 6. Carrier identity can be genuine ambient progress

A crucial action-classification correction follows.

If `E` is an effective Cartier divisor on a regular carrier `C`, then

```text
Bl_E(C) ~= C.
```

Nevertheless, if `C -> X` has positive codimension, then `E -> X` has
codimension at least two.  Blowing up `X` along `E` is generally nonidentity and
changes the embedding, normal bundle, projective-normal packet, contact debt,
and boundary ledger.

Therefore the final algorithm may contain steps that are

```text
identity on the lower-dimensional carrier,
nonidentity on the ambient scheme,
strictly decreasing on the packet rank.
```

The nonidentity gate must always be evaluated in the ambient scheme.  Rejecting
a carrier-Cartier step as “identity” would incorrectly discard the tangent-curve
cleaning sequence.

---

# 7. From flatification to a weighted ambient flatifier

Proper flatification can make the strict target flat after a carrier
modification

```text
C^flat -> C.
```

The bi-Rees comparison then leaves only finite exceptional saturation debt.
Let `K` be a carrier flatifier ideal and let `N` dominate the finite debt
profile.  The one-step generalized ambient object is expected to be a weighted
ideal of the form

```text
J_(K,N) = I_C + lift(K)^N
```

or, for a finite portfolio, the corresponding multiweighted sum/product.

In the tangent model,

```text
I_C=(x), K=(u), N=m,
J_(K,N)=(x,u^m).
```

The blowup of this nonregular thick centre makes the graph `x-u^m` terminal in
one weighted chart.  It is not an allowed final centre, but it is a useful
intermediate Rees modification.

After principalizing `K` in dimension `<dim X`, the weighted ideal becomes
monomial in regular normal and boundary parameters.  A characteristic-free
toroidal principalization word should dominate its blowup.  Every centre in
that word is a regular coordinate stratum contained in `C`, so active marked
legality follows from ideal-power monotonicity.  Flatness of the strict target
is preserved under the dominating base change.

This yields the new candidate theorem:

> **Ordinary Domination of a Weighted Ambient Flatifier.**  Every finite
> projective-normal flatifier with a certified saturation-debt bound admits a
> symmetry-compatible finite word of ordinary regular ambient blowups,
> contained in the raw candidate centre, whose composite dominates the
> weighted bi-Rees modification and whose final actual packet is the flat
> strict target up to invertible twists.

The theorem remains open.

---

# 8. Contact and passive safety become one portfolio

The regular-support intersection branch no longer needs an unrelated scalar
thickness algorithm.  For every anchor `Z_i`, retain the coherent contact ideal

```text
D_i = sum_(j != i) I_(Z_j) O_(Z_i),
```

or its finite presentation module.  Its strict target under a flatifying or
principalizing carrier modification is invertible or zero.  The difference
between that target and the actual ambient transform is again exceptional
saturation debt.

Thus one finite portfolio contains:

```text
passive projective-normal tail sheaves,
finite low associated-graded pieces,
anchor-contact modules,
log-conormal and boundary-contact modules,
Fitting/kernel residual modules.
```

Strict targets are flattened or principalized in lower dimension.  Actual
ambient packets are recovered by one common bi-Rees comparison and one common
saturation-debt ledger.

---

# 9. Corrected recursive architecture

```text
prepared intrinsic marked state
-> finite Frobenius-Hasse/conormal packet
-> minimizer intersection arrangement
-> raw regular candidate centre C

PROJECTIVE-NORMAL TARGET
-> finite prefix + projective Serre tail
-> proper flatification of the strict target on C
-> lower-dimensional regular domination of carrier flatifiers

ACTUAL AMBIENT REALIZATION
-> bi-Rees saturation comparison
-> finite exceptional saturation-debt portfolio
-> weighted ambient flatifier
-> regular toroidal ordinary-centre domination
-> actual passive-normal-flat / contact-clean / log-legal C'

CLEAN ARRANGEMENT
-> symmetry-compatible wonderful word
-> apply the same legalization compiler to every word centre
-> all-chart hereditary reconstruction without reset
-> dimension / saturation / contact / passive / debt / SCC rank
-> finite global ordinary word
-> principalization and resolution.
```

The X035 support-singular branch remains unchanged: singular reduced carriers
are processed by lower-dimensional relative resolution and ambient lifting.
X037 rewrites the regular-support and passive-legality branches.

---

# 10. Rank architecture

The local legalization rank now begins

```text
(ambient dimension,
 phase,
 carrier-support dimension,
 exceptional saturation-debt multiset,
 anchor-contact multiset,
 passive projective-tail defect,
 Hasse/Fitting/kernel profile,
 source/debt ledger,
 recurrent-SCC height,
 remaining word height).
```

A saturation drop must precede newly created boundary/debt coordinates.  The
four-coordinate arithmetic core

```text
(saturation, contact, passive, debt)
```

is formalized in `SaturationDebtRank.lean`.  The actual geometric theorem that
every nonterminal macro enters a strict branch is still open.

---

# 11. Lean source written in this round

```text
ExceptionalLayerTransform.lean
WeightedContactCleaning.lean
FinitePrefixTailCriterion.lean
SaturationDebtRank.lean
X037BiReesSaturationIndex.lean
X037BiReesSaturationIndexAudit.lean
```

The exact slice proves:

1. the image of a finite exceptional-layer endomorphism is the quotient by its
   kernel;
2. a certified saturation quotient is represented by a finite layer image;
3. weighted contact equations factor in the continuing and terminal chambers;
4. positive exceptional charge strictly lowers numerical debt;
5. a finite low-degree window plus an eventual tail covers all degrees;
6. the saturation/contact/passive/debt rank is well founded.

It proves none of the scheme-level transport or realization bridges.

---

# 12. Exact open frontier after X037

```text
X037-G1   PROJECTIVE_NORMAL_REES_SERRE_FINITE_PACKET
X037-G2   NESTED_REGULAR_NORMAL_LINE_TWIST
X037-G3   BIREES_COMPARISON_MAP_CONSTRUCTION
X037-G4   BIREES_EXCEPTIONAL_SATURATION_COMPARISON
X037-G5   COMPARISON_BASE_CHANGE_AND_OVERLAP
X037-G6   COHERENT_SATURATION_DEBT_FINITE_PORTFOLIO
X037-G7   WEIGHTED_AMBIENT_FLATIFIER_IDEAL
X037-G8   WEIGHTED_FLATIFIER_ACTUAL_PACKET_THEOREM
X037-G9   LOWER_DIMENSIONAL_MONOMIALIZATION_OF_FLATIFIER
X037-G10  REGULAR_TOROIDAL_DOMINATION_OF_WEIGHTED_BLOWUP
X037-G11  ACTIVE_AND_LOG_LEGALITY_OF_DOMINATING_WORD
X037-G12  PASSIVE_NORMAL_FLATNESS_AFTER_DOMINATION
X037-G13  ANCHOR_CONTACT_AS_SATURATION_DEBT
X037-G14  SOURCE_LABELS_AND_NO_RECHARGE
X037-G15  ALL_CHART_SATURATION_DEBT_DECREASE
X037-G16  LEGALIZATION_MACRO_HEREDITARY_REENTRY
X037-G17  WONDERFUL_WORD_LEGALIZATION
X037-G18  COMPOSITE_GLOBAL_RANK
X037-G19  UNIVERSAL_JOINTLY_LEGAL_ACTUAL_CENTRE_WORD
```

The highest-information cut is now

```text
X037-G4 + X037-G8 + X037-G10.
```

The first theorem identifies the exact discrepancy, the second proves that a
finite weighted lift removes it, and the third compiles that generalized lift
into allowed ordinary regular blowups.

---

# 13. Maximum-likelihood decisive theorem

> **Bi-Rees Saturation and Weighted Ambient Legalization Theorem.**  Let a
> prepared marked state on a smooth `n`-dimensional scheme over a perfect field
> of characteristic `p>0` produce a finite symmetry-stable family of raw
> regular candidate centres.  Assume the strong relative principalization
> program in dimensions `<n`.  For every raw centre and every finite passive,
> contact, boundary, and Fitting portfolio, construct a finite Rees--Serre
> packet and a proper flatification of its strict target.  The actual ambient
> packet after lifting the carrier word has the same exceptional saturation as
> that target; their discrepancy is a finite source-labelled exceptional-power
> torsion portfolio.  A finite weighted ambient bi-Rees modification removes
> the discrepancy, and a symmetry-compatible toroidal word of ordinary regular
> centres dominates that modification.  The final strict transform is
> simultaneously active-permissible, passive-normal-flat, Tor-safe,
> SNC-compatible, and nonidentity.  All packets and ledgers reconstruct on
> every chart and overlap without reset, and each nonterminal macro strictly
> lowers the composite dimension/saturation/contact/passive/debt/SCC rank.

This is the present maximum-likelihood replacement for the naive X036 ambient
flatification edge.  It is not proved.

---

# 14. Annals-series maximum-likelihood estimate

The modal form remains six papers, but the bi-Rees comparison and weighted
ambient realization become an independent major chapter.  The new central
estimate is **564 dense Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Wonderful Minimizer Arrangements, Anchor-Contact Portfolios, and Actual-Centre Synthesis | 118 |
| III | Bi-Rees Transport, Projective-Normal Flatification, and Weighted Ambient Legalization | 142 |
| IV | Exceptional Saturation Debt, Recurrent Classes, and Causal Termination | 88 |
| V | Global Descent, Symmetry-Compatible Toroidal Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **564** |

A one-volume editorial edition with the proof DAG, complete chart compendium,
counterexample atlas, theorem-interface cards, and paper-to-Lean map is
estimated at **615--650 physical pages**.

Subjective publication-form planning weights:

```text
six papers                              0.52
seven papers, splitting bi-Rees theory 0.30
five papers after consolidation        0.10
other                                   0.08
```

These are planning weights, not calibrated probabilities.

---

# 15. Truth boundary

```text
ROUND_ID                                             = MLEL-X037 / BRT-ESD

NAIVE_X036_STRICT_TRANSFORM_EDGE_REJECTED            = true
TANGENT_GRAPH_COUNTEREXAMPLE_IDENTIFIED              = true
EXCEPTIONAL_SATURATION_DEBT_IDENTIFIED               = true
WEIGHTED_AMBIENT_FLATIFIER_ROUTE_IDENTIFIED          = true
PASSIVE_CONTACT_BOUNDARY_PORTFOLIO_UNIFICATION       = CANDIDATE

EXCEPTIONAL_LAYER_LEAN_SOURCE_WRITTEN                = true
WEIGHTED_CONTACT_LEAN_SOURCE_WRITTEN                 = true
FINITE_PREFIX_TAIL_LEAN_SOURCE_WRITTEN               = true
SATURATION_DEBT_RANK_LEAN_SOURCE_WRITTEN             = true

BIREES_SATURATION_COMPARISON_PROVED                  = false
WEIGHTED_FLATIFIER_ACTUAL_PACKET_THEOREM_PROVED      = false
REGULAR_TOROIDAL_DOMINATION_PROVED                   = false
SATURATION_DEBT_NO_RECHARGE_PROVED                   = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED           = false

X037_CLEANROOM_GREEN                                 = false
NEW_DECLARATIONS_PROMOTED                            = false
CERTIFIED_GRAPH_CHANGED                              = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                   = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION           = false
FORMAL_GLOBAL_STATUS                                 = OPEN_GAP
```

---

# 16. Principal standard inputs

1. Strict transforms of closed subschemes and quasi-coherent modules under
   blowups; composition of strict transforms.
2. Blowup in an effective Cartier divisor is the identity on the carrier.
3. Relative Proj, Serre vanishing, cohomology and base change, and projective
   flattening stratification.
4. Raynaud--Gruson flatification and functorial proper flatification.
5. Characteristic-free principalization of monomial/toroidal ideals.
6. The current MLE--Lean baseline through X036 and the restricted
   Hasse--Morita core descent theorem.
