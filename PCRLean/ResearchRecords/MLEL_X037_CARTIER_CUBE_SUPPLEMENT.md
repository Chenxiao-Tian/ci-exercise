# MLEL-X037 / BRT-ESD — Cartier Torsion–Special-Fibre Induction

**Chinese title:** Cartier 扭曲–特殊纤维归纳与例外立方体合法化  
**Date:** 2026-08-04  
**Class:** `CANDIDATE_GRAPH_REFINEMENT / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

---

# 1. Executive correction

The first X037 formulation tried to identify the actual projective-normal
packet with a flat strict-transform target after removing exceptional torsion
and then refined the discrepancy to a two-sided lattice packet.  The lattice
packet is intrinsic and useful, but equality of lattices is stronger than the
property needed by the resolution algorithm.

The required property is flatness over the transformed centre.  Along an
effective Cartier exceptional divisor, flatness admits a much more economical
local criterion:

```text
flat away from the divisor
+ no divisor torsion
+ flat special fibre on the divisor
= flat everywhere.
```

Consequently the load-bearing ambient-flatification problem should be recast as
a **Cartier torsion–special-fibre induction**, not as a universal lattice
alignment theorem.

This changes the maximum-likelihood proof graph from

```text
actual lattice -> exact target lattice
```

to

```text
actual packet
-> exceptional torsion branch
-> lower-dimensional special-fibre branch
-> Cartier local criterion
-> actual flatness.
```

The two-sided lattice packet remains a finite diagnostic and elementary-
transform interface, but it is no longer required to vanish identically.

---

# 2. Finite-module Cartier flatness criterion

Let `A` be a Noetherian ring, let `t in A` be a nonzerodivisor, and let `M` be a
finite `A`-module.  The proposed exact affine theorem is:

> **Cartier Torsion–Special-Fibre Criterion.**  The module `M` is flat over
> `A` if and only if all three conditions hold:
>
> 1. `M_t` is flat over `A_t`;
> 2. multiplication by `t` on `M` is injective, equivalently
>    `Tor_1^A(A/(t),M)=0`;
> 3. `M/tM` is flat over `A/(t)`.

The forward implication is standard.  For the converse, localize at a prime
`p`.

* If `t` is not in `p`, condition (1) gives flatness.
* If `t` lies in `p`, work over the local Noetherian ring `A_p`.  The finite
  flat module `M/tM` is free.  Lift a basis to a map
  `A_p^r -> M_p`.  Its cokernel vanishes by Nakayama.  If `K` is its kernel,
  the Tor condition identifies `K/tK` with the kernel of the reduced basis map,
  hence `K/tK=0`; Noetherianity makes `K` finite and Nakayama gives `K=0`.
  Thus `M_p` is free.

For a coherent sheaf `F` on a locally Noetherian scheme `C` and an effective
Cartier divisor `E`, the sheaf form is:

```text
F flat over C
<->
F|_(C-E) flat,
I_E acts regularly on F,
F tensor O_E flat over E.
```

The finite-presentation hypothesis is automatic for the coherent graded pieces
in the present Noetherian setting.

---

# 3. Why lattice equality is unnecessary

Consider the two lattices

```text
O(-E) subset O
```

inside their common localization.  They differ along `E`, but both are locally
free and hence flat.  Likewise

```text
O directSum O(-E)
```

need not be aligned with `O^2` to satisfy the passive gate.

The correct question is therefore not whether the actual lattice equals the
flat target lattice, but whether the actual lattice has:

```text
zero E-torsion
and
flat reduction modulo E.
```

The two-sided intersection/sum packet detects the finite discrepancy, but only
its nonflat special-fibre and torsion parts require correction.

A contrasting example is the ideal `(u,v)` over `k[u,v]` with `E=(u)`.  The
module is torsion-free with respect to `u`, but its reduction modulo `u` has a
residual defect at `v=0`.  This defect lives on the strictly lower-dimensional
special fibre and is exactly the branch to which the recursion should descend.

---

# 4. Application to projective-normal packets

Let `C -> X` be a raw regular candidate centre and let a lower-dimensional
flatification word produce a regular transform `C^+ -> C` with exceptional SNC
divisor `E`.  For one passive owner let

```text
G^act = gr_(I_(C^+))(M^+)
```

be the actual associated-graded module after the ambient lift.

The proper flatification theorem supplies a flat strict target away from the
exceptional locus.  The bi-Rees comparison is only required to prove

```text
G^act|_(C^+-E) is flat.
```

The remaining obligations for each finite low graded piece and for the
projective Serre tail are:

```text
TORSION BRANCH
ker(I_E : G^act -> G^act) = 0;

SPECIAL-FIBRE BRANCH
G^act / I_E G^act is flat over E.
```

The torsion branch is the exceptional contact/saturation branch.  Its support,
annihilator, Fitting layers, and source-labelled exceptional order form a finite
packet.  The special-fibre branch is a coherent flatification problem on `E`,
whose dimension is one less than that of `C^+`.

Once both branches close, the Cartier criterion gives actual normal flatness.
No equality with the strict target is needed.

---

# 5. Finite Rees–Serre compression survives the correction

The infinite graded module is still finite-state.  For a finite graded module
over the symmetric algebra of the conormal bundle, choose a uniform Serre bound
`N`.  The passive packet consists of

```text
LOW DEGREES
G_0,...,G_N;

PROJECTIVE TAIL
F = tilde(G) on P(N_(C/X)).
```

For every low degree retain:

```text
E-torsion kernel,
special fibre G_n/I_E G_n,
off-E flatness certificate.
```

For the projective tail retain:

```text
H_E^0(F),
F tensor O_(P_E),
off-E flatness,
projective flattening data on P_E -> E.
```

Thus the Cartier correction does not reintroduce infinitely many conditions.
It replaces exact lattice alignment by a finite torsion/special-fibre packet.

---

# 6. The SNC exceptional cube

After a regular toroidal carrier word, the exceptional divisor is generally

```text
E = E_1 union ... union E_r
```

with simple normal crossings.  One Cartier criterion is not enough globally;
the correct finite object is the **Cartier cube**.

For every boundary subset `S`, let

```text
E_S = intersection_(i in S) E_i,
F_S = the successively reduced packet on E_S.
```

For every `i` not in `S`, retain the edge data

```text
Tor_1^(O_(E_S))
  (O_(E_(S union {i})), F_S)
```

and the child special fibre `F_(S union {i})`.  The complete cube records:

1. regularity of every boundary equation on the appropriate parent packet;
2. flatness of every terminal stratum packet;
3. compatibility under permutations, overlaps, and smooth base change.

Iterating the one-divisor local criterion over this finite cube proves flatness
of the root packet.  No arbitrary ordering of equal-depth components is needed:
the complete subset cube is symmetry stable, while an age/depth ordering is
used only for ordinary-centre serialization.

The same cube also packages logarithmic boundary compatibility.  Passive
normal flatness and log-SNC legalization are therefore two faces of one
boundary-stratified recursion.

---

# 7. Recursive legalization algorithm

The corrected local compiler is:

```text
LEGALIZE(C,F,E):

1. Rees--Serre compression.
   Replace every infinite graded passive packet by finitely many low pieces and
   one projective tail.

2. Off-boundary flatification.
   Construct a proper carrier modification whose strict target is flat.
   Resolve/principalize its centres in lower carrier dimension and lift the
   regular word ambiently.

3. Exceptional torsion extraction.
   On every new Cartier component E_i, form the finite source-labelled torsion
   and contact packet of the actual ambient transform.

4. Torsion cleaning.
   Principalize the torsion/contact carrier on E_i and lift its recursively
   legalized regular word ambiently.  Every positive exceptional charge lowers
   the corresponding saturation/contact layer.

5. Special-fibre recursion.
   Restrict the torsion-free actual packet to E_i and recursively flatify its
   finite low pieces and projective tail on the strictly lower-dimensional
   boundary stratum.

6. Cartier compilation.
   Apply the one-divisor criterion on each cube edge, from deepest strata back
   to the root.

7. Hereditary reconstruction.
   Recompute the full owner, source, age, debt, Hasse, Fitting, contact, and
   Cartier-cube packets on every chart and overlap without resetting old
   sources.
```

Every preparatory subcentre appearing in steps 2--5 is itself legalized by the
same procedure.  Its carrier dimension is strictly smaller, so the recursion is
not circular.

---

# 8. Termination rank

The local rank should be refined to

```text
(ambient dimension,
 carrier dimension,
 Cartier-cube depth,
 oldest exceptional-source age,
 exceptional torsion-layer multiset,
 special-fibre flatness/Fitting profile,
 anchor-contact profile,
 Hasse/kernel profile,
 ordinary source/debt ledger,
 recurrent-SCC height,
 remaining word height).
```

The strict branches are:

* recursive special-fibre or centre legalization lowers carrier dimension;
* insertion into a deeper Cartier stratum lowers remaining dimension;
* torsion cleaning lowers the oldest source-labelled exceptional layer;
* at fixed torsion, special-fibre flattening lowers its Fitting/flattening
  profile;
* ordinary debt cleanup lowers the final ledger coordinate.

The unresolved theorem is the no-recharge statement: a younger exceptional
component may be born, but an old Cartier source may not recover a layer already
consumed.  This is now the exact causal interface to the existing aged-ledger,
no-recharge, and no-infinite-birth machinery.

---

# 9. Revised load-bearing cut

The two-sided lattice comparison remains useful but is no longer the principal
completion gate.  The revised cut is:

```text
X037-C1  CARTIER_TORSION_SPECIAL_FIBRE_CRITERION
X037-C2  FINITE_REES_SERRE_CARTIER_PACKET
X037-C3  ACTUAL_PACKET_FLAT_OFF_EXCEPTIONAL_LOCUS
X037-C4  EXCEPTIONAL_TORSION_CONTROLLED_TRANSFORM
X037-C5  SPECIAL_FIBRE_RELATIVE_FLATIFICATION
X037-C6  SNC_CARTIER_CUBE_COMPILATION
X037-C7  RECURSIVE_AMBIENT_LEGALIZATION_OF_CUBE_CENTRES
X037-C8  CARTIER_SOURCE_NO_RECHARGE
X037-C9  GLOBAL_CUBE_RANK_DECREASE
```

The highest-information cut is now

```text
X037-C3 + X037-C4 + X037-C8.
```

`C1` is standard finite-module commutative algebra.  `C2` is relative
Serre/flattening theory.  The genuinely project-specific mathematics is the
actual ambient transform off the exceptional set, the strict consumption law
for exceptional torsion, and hereditary no recharge.

---

# 10. Revised decisive theorem

> **Cartier-Cube Ambient Legalization Theorem.**  Let a prepared marked state
> on a smooth `n`-dimensional scheme produce a finite symmetry-stable family of
> raw regular candidate centres.  Assume strong relative resolution and
> principalization in dimensions `<n`.  For every raw centre, compress every
> passive associated-graded portfolio into a finite Rees--Serre packet and
> flatify its strict target on the carrier.  After ambient lifting, the actual
> packet is flat away from the resulting SNC exceptional divisor.  Its complete
> Cartier cube has finite source-labelled torsion/contact packets on every edge
> and finite special-fibre flatness packets on every stratum.  A recursively
> legalized ordinary ambient-centre word kills every edge torsion packet and
> flatifies every special fibre.  Iterated Cartier local criteria then prove
> actual passive normal flatness at the root.  The same cube enforces log-SNC
> compatibility.  Every owner, source, debt, boundary, Hasse, Fitting, contact,
> and cube identity reconstructs on all charts and overlaps without reset, and
> every nonterminal macro strictly lowers the composite
> dimension/cube-depth/torsion/special-fibre/debt/SCC rank.

This theorem is the present highest-posterior local completion theorem.  It is
not proved.

---

# 11. Truth boundary

```text
CARTIER_FLATNESS_CRITERION_IDENTIFIED             = STANDARD_MATH_TARGET
LATTICE_EQUALITY_REQUIRED_FOR_FLATNESS            = false
FINITE_CARTIER_PACKET_IDENTIFIED                  = true
SNC_CARTIER_CUBE_IDENTIFIED                       = true
PASSIVE_AND_LOG_LEGALIZATION_UNIFIED              = CANDIDATE

ACTUAL_OFF_EXCEPTIONAL_FLATNESS_PROVED            = false
EXCEPTIONAL_TORSION_STRICT_CLEANING_PROVED        = false
SPECIAL_FIBRE_RECURSIVE_FLATIFICATION_PROVED      = false
CARTIER_SOURCE_NO_RECHARGE_PROVED                 = false
CARTIER_CUBE_AMBIENT_LEGALIZATION_PROVED          = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION        = false
FORMAL_GLOBAL_STATUS                              = OPEN_GAP
```
