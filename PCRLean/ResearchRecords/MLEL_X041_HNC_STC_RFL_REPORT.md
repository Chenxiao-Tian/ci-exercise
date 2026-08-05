# MLEL-X041 / HNC-STC-RFL

## Homogenized Normal-Cone Compactification, Strict-Transform Cofinality, and Regular-Flag Flat Lifting

**Chinese title:** 齐次化法锥紧化、严格变换共尾性与正则旗平坦提升  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X040 / CFT-ACN`  
**Primary D001 refinement:** `G29 -> G31 -> G41`, with direct reductions of `G56/G58` and the passive part of `G52/G53`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_COMPRESSION / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04 ET / 2026-08-05 UTC  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X040 correctly identified three obstacles:

```text
crossing flatifier centres;
hidden nonfunctorial choice of a flatifier;
loss of strict-transform semantics under arbitrary word compression.
```

The present round makes two further reductions.

## Reduction A — canonical proper packet without a Rees-Serre cutoff

The complete affine normal-cone module can be compactified canonically by one
homogenizing variable.  If

```text
S = Sym_C(E),          E = I_C/I_C^2,
G = gr_C(M),
Sbar = S[z] = Sym_C(O_C directSum E),
H(G) = G[z] with total grading,
```

then

```text
Pbar_C = Proj_C(Sbar) = P_C(O_C directSum E)
```

is proper over `C`, the standard open `D_+(z)` is the full affine normal cone
`Spec_C(S)`, and the coherent sheaf associated with `H(G)` restricts there to
the complete module `G` with every degree retained.

Moreover

```text
G is O_C-flat
iff
H(G)~ is C-flat.
```

Thus no arbitrary low-degree cutoff, Hilbert-polynomial tail, or
presentation-dependent transition window is needed.  The projective packet is
canonical, finite, all-degree, and compatible with flat base change.

## Reduction B — source-word realization is largely standard strict-transform
cofinality

Strict transform depends on its centre, but a finite centre word has a
distinguished composite blowup ideal whose support remembers the union of the
word centres.  Stacks Project, Divisors, Lemmas 31.34.3 and 31.34.6 show:

```text
iterated strict transform
=
strict transform for the centre-exact composite blowup;

once a transform is flat,
every later strict transform is its pullback.
```

More on Flatness, Lemma 38.30.6 uses exactly this mechanism together with a
finite product of local flatifier ideals to construct one common flatifying
blowup.  Therefore the X040 common-product strategy is not merely analogous to
standard flatification gluing; it is its exact scheme-theoretic pattern.

The new dominant project-specific edge is consequently the **Regular-Flag
Flat-Lift Theorem**.  It must transport normal flatness from a carrier through
the lower-dimensional regular centres used to realize the functorial
flatifier.

---

# 1. The canonical homogenized normal-cone packet

Let `C -> X` be a regular immersion with ideal `I`, and put

```text
E = I/I^2,
S = Sym_(O_C)(E).
```

For a finite owner module `M`, its normal module

```text
G_C(M) = gr_I(M) = directSum_(n>=0) I^nM/I^(n+1)M
```

is a finite graded `S`-module.  Define

```text
Sbar = S[z], deg(z)=1,
H(G) = G tensor O_C[z]
```

with total grading

```text
H(G)_d = directSum_(0<=n<=d) G_n z^(d-n).
```

The projective completion is

```text
Pbar_C = Proj_C(Sbar) = P_C(O_C directSum E),
Fbar_C(M) = tilde(H(G_C(M))).
```

## 1.1 Affine-chart recovery

On `D_+(z)` one has

```text
(Sbar_z)_0 ~= S,
(H(G)_z)_0 ~= G.
```

Hence

```text
D_+(z) ~= Spec_C(S),
Fbar_C(M)|_(D_+(z)) ~= tilde(G_C(M)).
```

The packet sees every low degree because the homogenizing coordinate is
invertible on this chart.  It is not a projective tail.

## 1.2 Finite presentation

If homogeneous elements `g_1,...,g_t` generate `G` over `S`, they generate
`H(G)` over `S[z]`.  Thus `H(G)` is finite graded and `Fbar_C(M)` is coherent on
a projective `C`-scheme.

## 1.3 Exact flatness equivalence

If `G` is flat over `C`, then `H(G)=G tensor O_C[z]` is flat over `C`; localization
and passage to degree zero on standard opens preserve flatness.  Thus
`Fbar_C(M)` is flat over `C`.

Conversely, if `Fbar_C(M)` is flat over `C`, its restriction to `D_+(z)` is
flat, so the affine module `G` is flat over `C`.

Therefore

```text
normal flatness of M along C
iff
flatness of the homogenized projective-normal sheaf.
```

The module-theoretic triangular flatness backend is formalized in
`HomogenizedGradedFlatness.lean`.

## 1.4 Flat base change

For a flat morphism `C'->C`, powers, quotients, symmetric algebras,
homogenization, Proj standard opens, and the associated sheaf commute with base
change.  Hence the construction is canonical for the smooth/etale category
needed by the resolution program.

The full relative-Proj and sheaf proof remains a scheme-level theorem
obligation.

---

# 2. Functorial flatification now applies directly

For the finite passive portfolio `{M_j}`, take

```text
Fbar_C^pass = directSum_j Fbar_C(M_j).
```

Add logarithmic, boundary, source-Cartier, and comparison modules by placing
them on proper identity components over `C`, or by a finite disjoint-union
proper packet.  Flatness of the total direct sum is equivalent to flatness of
all constituents.

David Rydh's functorial flatification theorem for coherent sheaves on proper
noetherian morphisms gives a sequence of blowups, supported outside the maximal
flat open, whose strict transform is flat.  The sequence is functorial with
respect to flat base change.  Smooth and etale maps are therefore included.

This closes the hidden-choice issue at the level of source modifications.
It does not give regular centres in positive characteristic; smooth centres in
Rydh's theorem are obtained only in characteristic zero.

The X040 finite Rees-Serre cutoff packet is therefore replaced by the
homogenized projective completion.  The affine normal-cone module remains the
semantic all-degree object, while its canonical homogenization is the proper
functoriality object.

---

# 3. Centre-exact compression of a source word

Strict transform depends on the centre, not merely on the underlying morphism.
This X037 warning remains correct.  The refinement is that a finite blowup word
has a **distinguished centre-exact composite ideal**, not an arbitrary ideal
representing the same morphism.

Let

```text
C_r -> ... -> C_1 -> C_0=C
```

be a finite source-labelled word.  By repeated composition-of-blowups, choose
the canonical word ideal produced by the construction, together with the
certificate that its set-theoretic centre is the union of the successive source
centres transported to `C`.

Stacks Project, Divisors, Lemma 31.34.6 then gives

```text
strictTransform_(word ideal)(F)
=
iteratedStrictTransform_(word)(F).
```

This is stronger than morphism-only compression and weaker than the false
statement that every ideal defining the same blowup yields the same transform.
Cartier-factor changes still require the zero-torsion hypothesis of Lemma
31.34.5.

---

# 4. Common-product cofinality

Let the finite maximal-carrier groupoid produce functorial source words with
centre-exact composite modification ideals `J_lambda`.  Lift them to ambient
trace ideals `K_lambda` and put

```text
K_common = product_lambda K_lambda.
```

The blowup of `K_common` factors through every source blowup.  This is the same
product-ideal mechanism used in Stacks Project, More on Flatness, Lemma 38.30.6
to glue finitely many local flatifiers.

If `F_lambda^flat` is the final flat source transform, then on any further
blowup dominating its source modification the strict transform is the pullback
of `F_lambda^flat`: flatness kills new exceptional power torsion.  Hence the
common blowup carries flat transforms for every source simultaneously.

If a regular lower-dimensional principalization word makes `K_common`
invertible, it factors through the common blowup by the universal property.
Applying strict-transform transitivity and flat pullback again shows that the
actual final transform along the regular word is the pullback of every
`F_lambda^flat`.

The abstract finite-portfolio backend is formalized in
`SourceWordCofinalityCompiler.lean`.  The scheme-level composite-ideal,
trace-ideal, and factorization interfaces remain to be formalized.

---

# 5. The lower-dimensional induction is cleaner than X040 stated

Let `C` be a maximal raw carrier in an `n`-dimensional ambient scheme.  Since the
centre action is nonidentity,

```text
dim C < n.
```

The functorial flatifier centres are supported away from the maximal flat open,
which contains the generic point of every regular component of `C`.  Their
support has dimension strictly smaller than `dim C`.

Apply the full strengthened relative principalization theorem in dimension
`<n` directly to the common source ideal on `C`, enrolling:

```text
all active restrictions;
all homogenized and affine normal-cone passive modules;
all boundary/logarithmic strata;
all contact/source/debt ledgers.
```

This produces a finite regular word on `C`.  There is no need for an unranked
same-dimensional repeated flatification loop.  Each carrier call is a genuine
outer dimension-induction call.

What remains is to prove that each regular centre of this lower-dimensional word
is legal when lifted to the ambient scheme.  Active marked permissibility is
ideal-power monotonicity.  Passive and logarithmic lifting are exactly the
Regular-Flag Flat-Lift problem.

---

# 6. Regular-Flag Flat-Lift

Let

```text
D subset C subset X
```

be regular immersions.  Etale-locally write

```text
I_C=(x_1,...,x_r),
I_D=(x_1,...,x_r,y_1,...,y_s)
```

as one regular sequence.  In the blowup of `D`, only the `y_j`-charts meet the
strict transform of `C`.  On the `y_1`-chart,

```text
x_i = y_1 x_i',
y_j = y_1 y_j'  (j>1),
I_(C')=(x_1',...,x_r').
```

Thus the old and new normal filtrations differ by the explicit exceptional
line twist `y_1^n` in degree `n`.

Suppose for every passive owner `M`:

```text
gr_C(M) is flat over C;
the Rees filtration sequences are Tor-safe for the blowup in D;
D is normally flat for the full induced carrier portfolio;
the flag is SNC-compatible with the boundary.
```

The expected chart theorem constructs

```text
(I_C^n M/I_C^(n+1)M) pulled to C'
  ~=
I_(C')^n M'/I_(C')^(n+1)M'
```

with the degree-`n` exceptional twist.  Flatness of the left side then proves
flatness of every new piece.  The direct-sum and homogenized outputs are
compiled in `DegreewiseFlagFlatLiftCompiler.lean`.

The open work is the construction of these equivalences from the explicit Rees
charts, their overlap equality, smooth-base-change naturality, and source-ledger
compatibility.

---

# 7. New proof architecture

```text
finite intrinsic state
-> clean finite raw-carrier arrangement
-> intrinsic maximal-carrier groupoid

for each maximal carrier C:
  complete affine normal module G_C
  -> canonical homogenization H(G_C)
  -> coherent sheaf on P_C(O directSum I/I²)

finite groupoid direct sum
-> Rydh functorial flatification source words
-> centre-exact composite word ideals
-> ambient trace ideals
-> invariant finite product K_common

support(K_common) has lower dimension
-> strengthened relative principalization in lower dimension
-> regular carrier word
-> ambient trace lift

strict-transform transitivity + flat pullback
-> simultaneous flat terminal source transforms

Regular-Flag Flat-Lift at every nested edge
-> exact degreewise normal transport
-> passive normal flatness through wonderful serialization

source arrangement completion
-> bad support-thickness recursion or clean deepest-first word
-> source-conservative all-chart reentry
-> support/source/flag/word and outer causal descent
-> finite global ordinary word.
```

---

# 8. Candidate-graph changes

The following X040 nodes are reduced.

```text
X040-G0A finite functorial Rees-Serre packet
  replaced by
X041-G1 canonical homogenized normal-cone compactification.

X040-G0B functorial proper flatifier source
  becomes a standard Rydh input after X041-G1.

X040-G7 full source-word realization
  splits into standard centre-exact strict-transform transitivity,
  common-product cofinality, flat pullback, and an exact scheme interface.
```

The remaining minimum cut is

```text
X041-G1  HOMOGENIZED_NORMAL_PACKET_SCHEME_THEOREM
X041-G2  FLATNESS_EQUIVALENCE_AND_FLAT_BASE_CHANGE
X041-G3  CENTRE_EXACT_WORD_IDEAL_AND_TRACE_INTERFACE
X041-G4  LOWER_DIMENSIONAL_FULL_PORTFOLIO_REALIZATION
X041-G5  REGULAR_FLAG_DEGREEWISE_TRANSFORM_ISOMORPHISM
X041-G6  REGULAR_FLAG_OVERLAP_AND_NATURALITY
X041-G7  SOURCE_CONSERVATIVE_ALL_CHART_NO_RESET
X041-G8  OUTER_BIRTH_AND_GLOBAL_RANK_HANDOFF.
```

The highest-information edge is now

```text
X041-G5 + X041-G6 + X041-G7.
```

Functorial flatifier existence and common-refinement persistence are no longer
the conceptual bottleneck.  The bottleneck is exact normal-filtration transport
through a nested legal regular flag and its hereditary identity.

---

# 9. Lean source written in this round

```text
HomogenizedGradedFlatness.lean
DegreewiseFlagFlatLiftCompiler.lean
SourceWordCofinalityCompiler.lean
HomogenizedCarrierRank.lean
X041HomogenizedNormalCofinalityIndex.lean
X041HomogenizedNormalCofinalityIndexAudit.lean
```

The exact slice proves only:

1. flatness of the triangular homogenized direct sum is equivalent to flatness
   of all original graded pieces;
2. degreewise linear equivalences transport flatness to the new associated
   graded module and its homogenization;
3. certified source-by-source equivalences transport a finite flat source
   portfolio to a common refinement;
4. the support/source/flag/word rank arithmetic is well founded.

No scheme-level theorem is promoted.

---

# 10. Counterexample ledger additions

```text
HNC-1  projective tail flat, low degree nonflat:
       rejected by the D_+(z) all-degree chart;

HNC-2  arbitrary ideal with the same blowup morphism:
       still forbidden; use the distinguished centre-exact word ideal;

HNC-3  flat source transform followed by another blowup:
       strict transform is pullback, so no new source torsion;

HNC-4  singular positive-characteristic Rydh centre:
       functorial flatification does not supply a final permissible centre;
       lower-dimensional regular realization remains necessary;

HNC-5  regular flag without Tor safety:
       degreewise filtration base change can fail;

HNC-6  normal flatness only on maximal carriers:
       nested persistence still requires Regular-Flag Flat-Lift and Hironaka
       transitivity;

HNC-7  common product omits one carrier component:
       support dimension need not drop;

HNC-8  source relabelling after compression:
       centre-exact word identity and lineage must remain immutable.
```

---

# 11. Annals-series maximum-likelihood estimate

The canonical homogenization removes the finite cutoff/tail comparison chapter,
while the strict-transform cofinality theorem moves several pages from
project-specific conjecture to standard scheme theory.  Regular-Flag Flat-Lift
remains a substantial all-chart chapter.

The central estimate returns to **550 dense Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Common Trace Products, Anchor-Contact Ideals, and Wonderful Actual-Centre Synthesis | 120 |
| III | Homogenized Normal-Cone Flatification, Strict-Transform Cofinality, and Hereditary Reentry | 130 |
| IV | Passive-Budget No-Recharge, Source-Debt Causality, and Dimension-Strict Termination | 84 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **550** |

A one-volume editorial edition with theorem-interface cards, source-word and
normal-cone ledgers, complete chart compendium, proof DAG, counterexample atlas,
and paper-to-Lean map is estimated at **598--632 physical pages**.

Subjective publication-form planning weights:

```text
six papers                                        0.68
seven papers, splitting Regular-Flag transport    0.17
five papers after consolidation                   0.10
other                                             0.05
```

These are planning weights, not calibrated probabilities.

---

# 12. Modal decisive theorem

> **Homogenized Normal-Cone Functorial Flatification and Regular-Flag
> Persistence Theorem.**  Let a prepared marked state on a smooth
> `n`-dimensional scheme over a perfect field of characteristic `p>0` produce a
> finite symmetry-stable clean arrangement of regular raw carriers.  For every
> maximal carrier and every passive owner, the complete normal associated-
> graded module admits a canonical coherent homogenization on the projective
> completion `P(O directSum I/I^2)`, whose flatness is equivalent to normal
> flatness and whose construction commutes with flat base change.  Functorial
> proper flatification of the finite maximal-carrier packet produces
> equivariant centre-exact source words.
>
> The finite product of their ambient trace word ideals is a common refinement
> with strictly lower-dimensional support.  Strong relative principalization
> in lower dimension realizes this modification by a finite ordinary word in
> regular jointly legal centres.  Strict-transform transitivity and flat
> pullback identify the actual final source transforms with the pullbacks of the
> functorially flat terminal transforms.
>
> For every nested regular flag formed during the realization or the later
> wonderful word, joint Tor, normal-flat, active, and logarithmic legality gives
> an all-chart degreewise exceptional-twist isomorphism between the old and new
> normal modules.  Hence passive normal flatness persists through every nested
> blowup.  Hironaka transitivity propagates it to every intersection stratum;
> disjoint steps are tautological.  All source, owner, boundary, contact, and
> debt identities reenter without reset, and every nonterminal macro strictly
> lowers the support/source/flag/word and outer causal rank.

This theorem is the current maximum-likelihood target.  It is not established.

---

# 13. Truth boundary

```text
ROUND_ID                                           = MLEL-X041 / HNC-STC-RFL

HOMOGENIZED_PROJECTIVE_NORMAL_PACKET_IDENTIFIED    = true
ALL_DEGREES_RECOVERED_ON_D_PLUS_Z                  = true
ARBITRARY_REES_SERRE_CUTOFF_REQUIRED               = false
RYDH_FUNCTORIAL_FLATIFICATION_INPUT_IDENTIFIED     = true
CENTRE_EXACT_STRICT_TRANSFORM_TRANSITIVITY_IDENTIFIED = true
COMMON_PRODUCT_FLATIFIER_PATTERN_IDENTIFIED        = true

HOMOGENIZED_FLATNESS_LEAN_BACKEND_WRITTEN          = true
DEGREEWISE_FLAG_COMPILER_LEAN_BACKEND_WRITTEN      = true
SOURCE_COFINALITY_LEAN_BACKEND_WRITTEN             = true
CARRIER_FLAG_RANK_LEAN_BACKEND_WRITTEN             = true

HOMOGENIZED_RELATIVE_PROJ_SCHEME_THEOREM_PROVED    = false
CENTRE_EXACT_WORD_TRACE_INTERFACE_LEAN_PROVED      = false
LOWER_DIMENSIONAL_FULL_PORTFOLIO_REALIZATION_PROVED = false
REGULAR_FLAG_FLAT_LIFT_PROVED                      = false
SOURCE_CONSERVATIVE_ALL_CHART_NO_RESET_PROVED      = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false

X041_CLEANROOM_GREEN                               = false
NEW_DECLARATIONS_PROMOTED                          = false
CERTIFIED_GRAPH_CHANGED                            = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                 = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

---

# 14. Principal standard inputs

1. Stacks Project, Divisors, Section 31.34, especially strict-transform
   definition and Lemmas 31.34.3, 31.34.5, 31.34.6, and 31.34.7.
2. Stacks Project, More on Flatness, Lemma 38.30.6 and Theorem 38.30.7.
3. Stacks Project, Constructions, Sections 27.8--27.10 on Proj and standard
   opens of graded rings and modules.
4. David Rydh, *Functorial flatification of proper morphisms*, arXiv:2501.08394,
   Theorem 1.1.
5. Classical Hironaka normal-flatness transitivity and regular-flag local
   normal forms.
6. The MLE--Lean research baseline through X040 and the restricted
   Hasse--Morita core descent theorem.
