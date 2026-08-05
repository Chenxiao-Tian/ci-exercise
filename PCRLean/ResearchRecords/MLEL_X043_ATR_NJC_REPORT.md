# MLEL-X043 / ATR-NJC

## Ambient Trace Realization, Normal-Jet Criteria, and Joint Legality Compilation
## 环境迹实现、法向射流判据与联合合法性编译

**Parents:** `MLEL-X042 / RFG-TVC`, `MLEL-X041 / CEW-SNR`, `MLEL-X041 / HNC-STC-RFL`, `MLEL-X040 / CFT-ACN`  
**Date:** 2026-08-05  
**Class:** standard regular-immersion and strict-transform closure + finite Hasse-jet legality theorem + inductive candidate-graph contraction  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X042 reduced the hereditary transform problem to a finite exactified
Tor--Valabrega comparison portfolio on a regular carrier. Its dominant open
interface was the realization of a carrier-side flatifying word by ordinary
ambient blowups in actual regular centres that are simultaneously
active-permissible, passive/Tor-safe, and logarithmically compatible.

X043 closes the *local ambientization and active-legality interfaces* in the
form needed by dimension induction.

1. If `D -> C -> W` are regular immersions, then `D -> W` is regular and the
   conormal sequence is split exact. Blowing up `W` in the same closed
   subscheme `D` has strict transform of `C` equal to `Bl_D(C)`. Thus a regular
   word on the carrier has a canonical ambient realization; no additional
   trace centre has to be invented.

2. For a marked ideal `(a,b)`, ambient divisibility along a regular
   subcentre `D subset C` is equivalent to finitely many Hasse-normal
   coefficient conditions of orders `< b` on `C`. Ordinary derivatives are
   not used. The intrinsic object is the truncated normal jet

   ```text
   (a + I_C^b)/I_C^b  subset  O_W/I_C^b.
   ```

   In an etale normal frame `x`, the condition is

   ```text
   partial_x^[alpha](a)|_C  subset  I_(D/C)^(b-|alpha|)
   for every |alpha|<b.
   ```

3. If `C` has normal crossings with the ambient SNC boundary and `D` has
   normal crossings with the induced boundary on `C`, then `D` has normal
   crossings with the ambient boundary. This is a regular-parameter theorem.

4. Enrolling the finite normal-jet families, the X042 exactified passive
   comparison portfolio, the induced boundary, the source labels, and the
   centre-exact modification ideal in the lower-dimensional call produces a
   regular carrier word. Its canonical ambientization is jointly legal. The
   word factors through the source flatifier because its composite
   modification ideal becomes invertible.

5. On every ambient blowup chart meeting the strict transform of the carrier,
   the actual successor comparison is the pullback of the prepared carrier
   mixed-Rees comparison, with the standard exceptional grading twist. X042
   universal exactification therefore identifies kernels, images, and
   cokernels after the ambient word. The all-chart successor packet reenters
   without a new transform defect.

The remaining dominant burden is no longer ambient trace realization. It is
now concentrated in:

```text
universal actual-centre synthesis,
support--thickness strict descent,
source-causal recurrent-class exit,
global well-founded termination,
and finite functorial globalization.
```

General arbitrary-dimensional positive-characteristic resolution is not
proved.

---

# 1. Canonical ambientization of a regular carrier centre

Let `W` be locally Noetherian, let `C subset W` be a regular closed
subscheme, and let `D subset C` be a regular closed subscheme. Write

```text
I = I_(C/W),
J = I_(D/W),
L = I_(D/C)=J/I.
```

## Theorem 1.1 — Regular trace theorem

The composite immersion `D -> W` is regular. There is a split exact conormal
sequence

```text
0 -> (I/I^2)|_D
  -> J/J^2
  -> L/L^2
  -> 0.
```

### Proof

Composition of regular immersions is regular in the locally Noetherian
category. The conormal sequence is exact and locally split because the last
term is finite locally free. Etale locally one may choose a regular parameter
system

```text
x_1,...,x_r,y_1,...,y_s,z_1,...,z_t
```

with `C=(x_1,...,x_r)` and
`D=(x_1,...,x_r,y_1,...,y_s)`. The sequence is then the evident split sequence
on the classes of the `x` and `y` parameters.

## Theorem 1.2 — Ambient blowup realizes the carrier blowup

Let `W'=Bl_D(W)`. The strict transform `C'` of `C` is canonically

```text
C' = Bl_D(C).
```

On every standard chart meeting `C'`, the pivot is one of the parameters
normal to `D` inside `C`. If `q` is the pivot and `B` is the chart algebra,
then

```text
I B = q I_(C'/W').
```

### Proof

The strict-transform theorem identifies the strict transform of a scheme with
its blowup in the inverse-image centre. In the adapted coordinates, a chart
whose pivot lies entirely in `I` has empty intersection with `C'`; on a
`y`-pivot chart one has

```text
x_i = q (x_i/q),
```

and the quotients `x_i/q` generate the transformed carrier ideal.

## Consequence

A finite word of regular carrier centres has a canonical ambient word obtained
by blowing up the same closed subschemes. Its carrier strict transform is the
original carrier word at every stage. The ambient word is centre-exact and is
compatible with smooth and etale base change.

---

# 2. Finite normal-jet criterion for active marked divisibility

Let `a subset O_W` be a coherent ideal and let `b>=1`. Let `C subset W` be a
regular immersion with ideal `I`.

The intrinsic truncated normal jet is

```text
J_C^{<b}(a) = (a + I^b)/I^b  subset  O_W/I^b.
```

It is a finite filtered `O_C`-module. Its associated graded is presented in an
etale normal frame by Hasse coefficients.

Choose etale locally normal parameters `x=(x_1,...,x_r)` for `C`. Every local
section `f` has a finite normal Taylor expansion modulo `I^b`:

```text
f = sum_(|alpha|<b)
      partial_x^[alpha](f)|_C x^alpha
    mod I^b.
```

Here `partial^[alpha]` denotes the Hasse derivative. This identity is valid in
all characteristics and does not divide by factorials.

## Definition 2.1 — Normal-coefficient filtration

For `0<=n<b`, let `H_{C,n}(a)` be the finite `O_C`-submodule of

```text
Sym^n(I/I^2)
```

generated by the order-`n` normal Hasse coefficients of local sections of
`a`. Equivalently, retain the entire filtered module
`J_C^{<b}(a)`; the individual `H_{C,n}` are a frame presentation of this
intrinsic jet.

For a finite marked Rees family, take the finite union over a set of homogeneous
generators and all orders below their marks.

## Theorem 2.2 — Finite normal-jet legality criterion

Let `D subset C` be regular and put `L=I_(D/C)`. Then the following are
equivalent:

1. `a subset I_D^b` in `O_W`;
2. the image of `J_C^{<b}(a)` in `O_W/(I^b+I_D^b)` is zero;
3. in one, hence every, etale normal frame,

   ```text
   partial_x^[alpha](a)|_C
     subset L^(b-|alpha|)
   for every |alpha|<b;
   ```

4. the centre `D` is permissible for the finite normal-coefficient marked
   family on `C`.

### Proof

If `a subset I_D^b`, every Hasse coefficient of normal order `n<b` has
`L`-order at least `b-n`.

Conversely, write a local section `f in a` modulo `I^b` as the displayed Hasse
Taylor expansion. Every term

```text
c_alpha x^alpha
```

lies in `I_D^b` because

```text
c_alpha in L^(b-|alpha|),
x^alpha in I^|alpha| subset I_D^|alpha|.
```

The remainder lies in `I^b subset I_D^b`. Thus `f in I_D^b`.

The filtered module `J_C^{<b}(a)` is intrinsic. A change of normal frame acts
by an invertible block-triangular change on the finite Hasse coefficient
family, so the condition is frame independent. Formation commutes with smooth
and etale base change.

## Significance

Ambient active permissibility of a subcentre of `C` is therefore a finite
lower-dimensional condition. It is not inferred from the restriction
`a O_C`; the full truncated normal jet is retained. This removes the hidden
failure in the naive implication

```text
a O_C subset I_(D/C)^b  =>  a subset I_D^b,
```

which is false without the normal coefficients.

---

# 3. Logarithmic trace compatibility

Let `E` be an SNC divisor on regular `W`. Suppose `C` has normal crossings with
`E`, and let `E_C` be the induced ordered boundary on `C`.

## Theorem 3.1 — Logarithmic ambientization

If `D subset C` is regular and has normal crossings with `E_C`, then `D` has
normal crossings with `E` in `W`. After blowing up `W` in `D`, the strict
transform `C'` has normal crossings with the transformed boundary, and the
induced boundary on `C'` is the boundary obtained by blowing up `(C,E_C)` in
`D`.

### Proof

At a point of `D`, choose a regular parameter system in which the ambient
boundary components, the ideal of `C`, and the additional ideal of `D` in `C`
are generated by subsets of the parameters. Their union is again part of a
regular parameter system. Standard blowup coordinates preserve this property.

---

# 4. The joint legality portfolio

For a regular carrier `C`, define the finite joint portfolio

```text
JLeg(C) =
  source-flatifier composite modification ideal
  + finite normal-Hasse coefficient families of all active marks
  + X042 exactified Tor-Valabrega comparison portfolio
  + complete homogenized normal modules
  + induced logarithmic boundary data
  + anchor-contact and support-thickness packets
  + source, owner, and exceptional-history labels.
```

The support of the modification and comparison defects is disjoint from the
good generic locus, hence has dimension strictly smaller than `dim C`.

## Theorem 4.1 — Inductive ambient regular trace realization

Assume the full-portfolio principalization and preparation theorem in dimensions
strictly smaller than `dim C`. Then there is a finite word of blowups on `C`
with regular centres, supported on the bad locus, such that:

1. the composite modification ideal of the source flatifier becomes invertible,
   so the word factors through the source flatifier;
2. every normal-jet legality condition for every active marked generator holds;
3. the complete exactified passive comparison portfolio is flat and its three
   defect modules vanish;
4. every centre has normal crossings with the induced boundary;
5. all source and history labels are retained.

Blowing up the same closed subschemes in `W` gives a finite word of ordinary
ambient blowups in actual regular jointly legal centres.

### Proof

Apply the lower-dimensional theorem to the finite portfolio `JLeg(C)`. Every
centre lies in a closed subset of dimension `< dim C`. The modification ideal
becomes invertible, hence the resulting word factors through its blowup by the
universal property. The finite normal-jet criterion gives ambient active
marked divisibility. X042 universal exactification and flat-kill give passive
normal flatness and Tor safety. The logarithmic ambientization theorem gives
boundary compatibility. The regular trace theorem and the strict-transform
theorem ambientize the word without changing its carrier semantics.

## Corollary 4.2 — No independent ambient-realization gap

Regular ambient trace realization is an inductive compiler, not a new
same-dimensional existence theorem. Once the bad carrier support is strictly
smaller-dimensional and the complete portfolio is passed to the recursive
call, the ambient centres are the same regular subschemes produced on the
carrier.

---

# 5. Successor comparison identification

Consider one centre `D subset C subset W` of the joint word. On every ambient
chart meeting `C'`, the chart algebra restricts to the corresponding chart of
`Bl_D(C)` and

```text
I_C B = q I_C'.
```

The old normal piece, the image-filtration core, and the new strict-carrier
normal piece are therefore the same objects used in the X042 carrier
comparison. The actual ambient controlled transform supplies the prescribed
exceptional twist.

## Theorem 5.1 — Ambient successor comparison

After the joint preparation of Theorem 4.1, the pullback of the prepared
exactified mixed-Rees comparison diagram is canonically the comparison diagram
of the actual successor carrier and actual controlled strict transforms. Thus
for every owner and every degree,

```text
I_C'^n M' / I_C'^(n+1) M'
  ~= pullback(I_C^n M/I_C^(n+1)M) tensor O_C'(nE).
```

The isomorphisms are multiplicative, agree on chart overlaps, preserve source
and boundary labels, and commute with smooth and etale base change.

### Proof

The strict transform of the carrier is the carrier blowup. The chart identity
`I_C B=qI_C'` gives the twist. The image filtration is constructed from the
same Rees algebra on both sides. The exactified kernels, images, and cokernels
commute with the centre-exact pullback, and they vanish after preparation.
Charts whose pivot is normal to `C` do not meet `C'`; on the remaining charts,
pivot changes differ by units, so the comparisons agree on overlaps.

## Corollary 5.2 — All-chart state reentry for a completed joint word

The active Hasse state, the passive normal system, the zero comparison
certificates, the boundary, the contact packet, and all source/history labels
reconstruct an intrinsic successor packet on every chart. No active,
passive, logarithmic, or source component is reset.

---

# 6. Candidate-graph contraction

## Closed or reduced to standard/inductive inputs

```text
X043-G1  composition of regular immersions and split conormal sequence
X043-G2  ambient blowup restricts to the carrier blowup
X043-G3  finite intrinsic truncated normal-jet packet
X043-G4  Hasse normal-jet criterion for ambient marked divisibility
X043-G5  logarithmic ambientization of a regular carrier centre
X043-G6  lower-dimensional full-portfolio realization of a carrier flatifier
X043-G7  ambient joint legality of the realized word
X043-G8  actual successor comparison identification
X043-G9  all-chart reentry after a completed joint word
```

## Remaining load-bearing nodes

```text
X043-G10  universal finite actual-centre arrangement for every nonterminal state
X043-G11  support--thickness and anchor-contact strict descent in all wild cases
X043-G12  geometric birth realization with no free source cloning
X043-G13  recurrent-class exit including immediate-defect branches
X043-G14  one strict global well-founded rank for every macro
X043-G15  finite Zariski/etale descent and symmetry-compatible serialization
X043-G16  final principalization and functorial resolution
```

## Highest-information next cut

```text
UNIVERSAL ACTUAL-CENTRE SYNTHESIS
  -> SUPPORT/THICKNESS/CONTACT COVERAGE
  -> SOURCE-CAUSAL GLOBAL TERMINATION.
```

---

# 7. Updated rank architecture

Ambient trace realization and exceptional recharge are removed as independent
rank coordinates. A current front segment is

```text
ambient dimension,
maximal unresolved carrier dimension,
dimension of the joint-legality defect support,
normal-jet legality profile,
Tor-Valabrega-Fitting profile,
support-thickness profile,
contact height,
unresolved source multiset,
Frobenius/Fitting defect multiset,
recurrent-class height,
centre-word height.
```

The normal-jet profile is finite because each active mark contributes only
orders below the mark. It vanishes exactly when the candidate carrier centre
is ambiently active-permissible.

---

# 8. Effect on the projected papers

The modal six-paper architecture is retained, with Paper III and Paper IV
rebalanced.

1. **Singularity Resolution in Positive Character I:** Intrinsic
   Frobenius--Hasse States, Conormal Packets, and Projectivity Discriminants.
2. **Singularity Resolution in Positive Character II:** Actual Centres,
   Support--Thickness Stratification, and Wonderful Arrangements.
3. **Singularity Resolution in Positive Character III:** Normal-Jet Legality,
   Mixed-Rees Comparison, and Hereditary Transform.
4. **Singularity Resolution in Positive Character IV:** Source Causality,
   Recurrent-Class Exit, and Well-Founded Descent.
5. **Singularity Resolution in Positive Character V:** Global Serialization,
   Principalization, and Descent.
6. **Singularity Resolution in Positive Character VI:** Functorial Resolution
   over Perfect Fields.

The current central estimate is approximately `548` dense
Annals/AMS-equivalent pages for the self-contained series. A unified article
shares all preliminaries and is expected to be substantially shorter.

---

# 9. Truth boundary

```text
REGULAR_CARRIER_WORD_AMBIENTIZATION               = closed
FINITE_NORMAL_HASSE_JET_LEGALITY_CRITERION         = closed
LOGARITHMIC_TRACE_COMPATIBILITY                    = closed
AMBIENT_JOINT_LEGALITY_FROM_LOWER_DIMENSION        = conditional-inductive closed
SUCCESSOR_COMPARISON_IDENTIFICATION                = conditional on X042 exactification
ALL_CHART_REENTRY_AFTER_COMPLETED_JOINT_WORD       = conditional-inductive closed

UNIVERSAL_ACTUAL_CENTRE_SYNTHESIS                  = open
FULL_SUPPORT_THICKNESS_COVERAGE                    = open
GLOBAL_SOURCE_CAUSAL_TERMINATION                   = open
FINITE_FUNCTORIAL_GLOBALIZATION                    = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```
