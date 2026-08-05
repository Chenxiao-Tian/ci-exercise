# MLEL-X046 / PDS-AST-IDE-FINAL

## Prime-Defect Shadow Towers, Alteration-Shadow Descent, and Independent-Defect Effectivity
## 素缺陷影子塔、变更影子下降与独立缺陷有效化

**Parents:** MLEL-X045 / AEF-NUB-CRX-FINAL; MLEL-X044 / COP-PCH-UCS-FINAL; CDX-022 / RCE-OR; AFPM-005 / NIB-GEN; valuation/local-uniformization line.  
**Date:** 2026-08-05  
**Class:** standard prime-layer valuation reduction + finite event-visible shadow hull + alteration-shadow exactification + candidate independent-defect effectivity theorem.  
**Global status:** `OPEN_GAP`.

---

## 0. Executive verdict

X045 conditionally terminates the entire finite coherent recurrent subgame and reduces every hypothetical infinite branch to a genuine class-V valuation/immediate-defect token. X046 attacks exactly this remaining class.

The main outcome is a further categorical contraction.

1. The finite coloured state sees only finitely many valuation observables: marked coefficients, Hasse coefficients, effective key degrees, conormal and Fitting minors, ramification/conductor shadows, source labels, and the common-model class. On a quasi-compact valuation neighbourhood these observables admit one finite event-visible shadow hull on a finite common model.

2. Any finite projection or alteration extension can be refined into a finite tower of prime-degree layers. Defect is multiplicative in towers; a nontrivial total defect is witnessed in at least one prime-degree layer. Thus class V may be analysed one prime layer at a time.

3. Prime layers fall into four typed routes:

   ```text
   DEFECTLESS:
       apply defectless multiplicity reduction or Abhyankar/monomial local
       uniformization;

   PURELY INSEPARABLE:
       enter the existing Frobenius/radicial debt branch;

   DEPENDENT ARTIN-SCHREIER DEFECT:
       reduce, through the dependent-defect classification, to a purely
       inseparable/radicial shadow;

   INDEPENDENT PRIME DEFECT:
       retain a differential-ramification shadow portfolio consisting of
       ramification ideals, Kahler-differential annihilators, trace ideals,
       coefficient cuts, and source/common-model data.
   ```

4. A single ramification ideal is not a complete higher-degree detector. The X046 packet is deliberately a finite portfolio. In particular, nontrivial defect of degree `p^2` need not force a nonprincipal ramification ideal.

5. Local uniformization after finite extension or purely inseparable alteration supplies a finite portfolio of uniformizing alteration charts over a quasi-compact valuation neighbourhood. The modification and the complete event-visible packet upstairs define a bounded alteration-shadow complex downstairs. Its coherent cohomology and Fitting layers form the alteration-shadow portfolio.

6. Defectless and dependent layers are absorbed by already existing branches. For an independent prime layer, every nonzero event-visible shadow either:

   ```text
   strictly enlarges a fixed coherent shadow ideal in a Noetherian ancestor;
   lowers effective key degree, conductor height, support dimension, or
     differential/ramification profile;
   changes the prime-layer or common-model class;
   or becomes invisible to every operation in the complete finite packet.
   ```

   Noetherian ACC terminates the first alternative.

7. The remaining decisive theorem is now precise:

   > **Independent-Defect Effectivity (IDE).** A stable independent prime-defect packet which is still visible to the complete finite coloured state has a nonzero coherent alteration shadow whose X044 actual-centre block changes its prime-layer shadow profile on every valuation in the certified neighbourhood. If every alteration shadow is invisible, the current finite packet is already terminal or descends from the uniformized alteration.

Under IDE, UDE-EV follows, class V acquires a strict ordinal, and X045 completes the global recurrence proof. IDE is not proved in the current baseline.

General arbitrary-dimensional positive-characteristic resolution remains open.

---

## 1. Event-visible valuation shadow hull

Let `X` be a finite-type integral model with function field `K`, let `V` be a quasi-compact subset of its Riemann--Zariski space, and let `P(Sigma)` be the complete finite coloured state complex.

### Definition 1.1 -- Event-visible observables

The event-visible valuation observables are the finite data needed to evaluate every constructor in the current state:

```text
values and initial forms of finitely many marked generators;
normal and directional Hasse coefficients below the finite marks;
finite Fitting minors and conormal relations;
effective key degrees and the finite coefficient basis used by the packet;
Frobenius/radicial exponents;
ramification and conductor shadows attached to the chosen finite projections;
source joins and immutable projection/common-model ancestry.
```

### Theorem 1.2 -- Finite shadow-hull theorem

There exists a finite sequence of proper models dominating `X` and one finite common model `X_sh` on which every event-visible observable is represented by a coherent ideal, a finitely presented module, or a finite graded packet. The construction is uniform on a finite constructible cover of `V` and is compatible with open restriction and smooth/etale base change.

### Proof

The state contains finitely many algebraic expressions and finite presentations. Each valuation has a model on which the finitely many relevant coefficients, centres and normalized finite extensions are defined. The corresponding centre conditions give constructible neighbourhoods in the Riemann--Zariski space. Quasi-compactness yields a finite subcover. A common proper modification dominates the finitely many models; on a Noetherian model the finite presentations and their Fitting ideals are coherent. Smooth/etale base change preserves the finite constructions.

### Boundary

The shadow hull records only the finite state-visible portion of an immediate-defect pro-end. It does not represent the full nonprincipal ramification cut as one coherent ideal.

---

## 2. Prime-degree defect tower

Let `L/K` be a finite extension arising from a finite projection, normalization, or alteration chart, and let `w` extend a valuation `v`.

### Theorem 2.1 -- Prime-layer reduction

After separating the purely inseparable part and passing to a finite normal closure of the separable part, the valued extension admits a finite tower

```text
K=K_0 subset K_1 subset ... subset K_m=L'
```

whose nontrivial layers have prime degree. The ramification index, residue degree, and defect are multiplicative in the tower. If the total extension has nontrivial defect, at least one prime layer has nontrivial defect.

### Consequence

The class-V packet is replaced by a finite ordered prime-layer shadow tower. A layer which becomes defectless is deleted. A purely inseparable layer is routed to the radicial/Frobenius packet. A Galois degree-`p` defect layer is classified as dependent or independent.

The tower is part of the immutable valuation ancestry. Refining or regrouping it does not create a new source.

---

## 3. Dependent defect is a radicial shadow

For an Artin--Schreier defect extension of prime degree in equal positive characteristic, the dependent/independent classification distinguishes those defect extensions which are connected to immediate purely inseparable extensions from those which are not.

### Candidate Theorem 3.1 -- Dependent-shadow reduction

For the event-visible packet, a dependent Artin--Schreier prime layer admits a finite purely inseparable shadow extension with the same relevant distance/ramification threshold. After passing to the finite shadow hull, its coefficient and Hasse data enter the existing radicial debt packet. Every leaf either lowers the radicial exponent, enlarges a fixed Frobenius coefficient ideal, or exits to a defectless/coherent class.

### Status

The valuation-theoretic classification is standard. The exact conversion of the related purely inseparable extension into one owner-safe ordinary-centre word on the original model remains part of the existing radicial actual-centre theorem. X046 does not count dependent defect as a new fifth geometric mechanism.

---

## 4. Independent-defect differential-ramification portfolio

For a prime-degree independent defect layer `L_i/K_i`, let `O_i subset O_(i+1)` be the corresponding valuation rings. The intrinsic valuation-theoretic data include:

```text
ramification ideals;
annihilators and Fitting ideals of Omega_(O_(i+1)/O_i);
traces of maximal and ramification ideals;
Dedekind/different shadows;
Artin-Schreier or Kummer coefficient-distance data;
source, projection and common-model ancestry.
```

Known characterizations of independent defect use several of these objects. They are retained together rather than collapsed to one ideal.

### Definition 4.1 -- Differential-ramification shadow portfolio

On a finite shadow model `A -> B`, choose finite presentations of the integral-algebra approximation, the relative differential module and the event-visible coefficient modules. Define

```text
DRSh(B/A)=
  {Fitt_j(Omega_(B/A)),
   Ann(Omega_(B/A)),
   Fitt_j(B/Tr(B)),
   contracted ramification and conductor ideals,
   coefficient-threshold ideals,
   prime-layer source data}.
```

All entries are coherent on the finite model. Enlarging the model transports the same labelled portfolio.

### Warning 4.2

A nonprincipal ramification ideal is an important prime-degree signal but is not a complete detector in arbitrary higher degree. The entire prime-layer portfolio is retained, and the total tower is composed only after each layer is typed.

---

## 5. Uniformizing alteration portfolio

Every valuation admits local uniformization after a finite extension of the function field, and also after a purely inseparable alteration. Abhyankar valuations admit local uniformization without such an extension under the standard separability hypotheses. A defectless finite projection admits multiplicity reduction along the valuation.

### Construction 5.1 -- Finite uniformizing portfolio

For each valuation in `V`, choose one of the following certified charts:

```text
defectless projection chart;
Abhyankar/quasi-monomial chart;
finite-extension local-uniformization chart;
purely inseparable alteration chart.
```

Require the chart to monomialize the finite event-visible packet, not merely to regularize the ambient local ring. Quasi-compactness extracts finitely many charts. Take finite common models for the bases and for the finite prime-layer towers.

The output is a finite alteration portfolio

```text
{f_a:Y_a -> X_a,
  prime-layer tower_a,
  monomial packet_a,
  source and valuation ancestry_a}.
```

This is a diagnostic and comparison object. It is not yet a resolution of the original model.

---

## 6. Alteration-shadow complexes

Let `f:Y->X` be one uniformizing alteration chart and let `P_X` be the finite coloured packet on `X`. Let `P_Y^mon` be its prepared monomial form on `Y`.

### Definition 6.1 -- Layerwise shadow complex

For each prime layer define a bounded complex `Sh_i` on the lower model:

```text
defectless layer:
  trace/norm and multiplicity-reduction comparison;

purely inseparable or dependent layer:
  Frobenius-contraction and radicial-debt comparison;

independent layer:
  differential-ramification portfolio and coefficient-shadow comparison.
```

All kernels, images, cokernels and trace/Frobenius comparison modules are exactified as in X042 before any nonflat descent.

### Theorem 6.2 -- Shadow-octahedron

The shadow complex of the full finite extension tower has a finite filtration whose graded factors are the transported prime-layer shadow complexes.

### Proof

Compose the layerwise comparison morphisms and apply the octahedral event theorem from X045. The tower is finite, so the filtration is finite.

### Definition 6.3 -- Downstairs alteration shadow

Let `Sh(f,P)` be the resulting bounded complex on the finite base model after proper pushforward and exactification. Its coherent cohomology sheaves and all intrinsic Fitting layers form the downstairs alteration-shadow portfolio.

The support of this portfolio is the locus on which the uniformized monomial packet fails to descend through the typed prime-layer comparisons.

---

## 7. Noetherian shadow descent

Fix one prime-layer type, one source label, one common-model class and every earlier geometric coordinate. Transport all coherent alteration shadows to a fixed Noetherian ancestor shadow envelope `U_V`.

Let

```text
0 = S_0 subset S_1 subset S_2 subset ... subset U_V
```

be the consumed alteration-shadow submodules. A genuinely new visible shadow gives a nonzero quotient of `U_V/S_n`; its inverse image strictly enlarges `S_n`.

### Theorem 7.1 -- Visible-shadow ACC

There are only finitely many genuinely new coherent alteration shadows in a fixed independent prime-layer recurrent class.

### Proof

`U_V` is a finite module over the finite ancestor shadow algebra. Strictly new shadows produce a strictly increasing submodule chain. Noetherian ACC terminates the chain.

### Consequence

A recurrent independent-defect branch with all earlier coordinates fixed eventually reaches a stable visible-shadow chamber. At that stage every event-visible coefficient, differential, ramification and Fitting shadow is inherited.

---

## 8. Independent-Defect Effectivity

The final nonstandard interface is the following.

### Candidate Theorem 8.1 -- Independent-Defect Effectivity (IDE)

Let a stable independent prime-defect token be represented by a quasi-compact valuation neighbourhood, a fixed prime-layer ancestry, a finite common model and its complete stable differential-ramification shadow portfolio. Assume the current coloured state is nonterminal on every neighbourhood component.

Then at least one of the following holds uniformly after a finite constructible refinement:

1. a nonzero proper coherent alteration shadow lies in the current joint marked locus; its X044 source-closed actual-centre block strictly lowers the alteration-shadow Fitting profile;
2. effective key degree, Frobenius/radicial exponent, conductor height or valuation-support dimension strictly drops;
3. the selected finite projection becomes defectless or the valuation becomes Abhyankar/quasi-monomial;
4. the prime-layer tower or common-model pro-isomorphism class changes;
5. every alteration shadow is invisible to the complete finite state, in which case the monomial packet on the uniformizing alteration descends to the current packet and the state is terminal for this token.

The centre word is ordinary, regular, jointly legal, source-conservative and uniform on the whole certified valuation neighbourhood.

### Maximum-likelihood proof route

- If a shadow is nonzero, its support is coherent and proper. Enrol all of its Fitting, active normal-jet, passive and boundary colours in the X044 portfolio and execute the lower-dimensional actual-centre block.
- Exactified shadow comparison makes the transform of the shadow equal to the successor shadow. Flat-kill eliminates a generically zero shadow; otherwise the projectivity/Fitting profile decreases.
- If all coherent shadows stabilize, compare with the finite uniformizing alteration. The upstairs packet is monomial. Any downstairs nonterminal coloured obstruction would contribute a nonzero kernel, cokernel, differential, trace or Frobenius comparison layer and hence a visible shadow. Therefore a completely invisible stable tail cannot support the current nonterminal packet.

### Truth boundary

The final implication in the last bullet is the load-bearing descent statement. It requires a semantically complete alteration-shadow complex and exact descent through independent defect. This is not presently proved in the research baseline.

---

## 9. UDE-EV and the class-V ordinal

Assuming IDE, define the class-V profile

```text
rho_V=
  (valuation-support dimension,
   prime-layer tower height,
   number and position of independent defect layers,
   effective key degree,
   Frobenius/radicial exponent,
   conductor/ramification profile,
   alteration-shadow Fitting profile,
   ancestor shadow-envelope height,
   common-model class,
   local escape-word height).
```

Use the well-founded foundation rank of strict coherent-shadow enlargement rather than the shadow ideal ordered by inclusion. Combine the finite numerical coordinates lexicographically and the finite prime-layer profiles by multiset extension.

### Conditional Theorem 9.1 -- UDE-EV

IDE yields a finite actual centre tree for every class-V token. On every nonterminal leaf `rho_V` strictly decreases or the packet enters the coherent X045 subgame.

### Conditional Theorem 9.2 -- Full recurrent termination

Place all class-V labels above the coherent labels and use the Dershowitz--Manna multiset extension. X045 coherent descent and Theorem 9.1 give a strict global recurrence multiset on every chart. Hence no infinite branch exists.

---

## 10. Candidate-graph contraction

### Closed or reduced to standard input

```text
finite event-visible valuation shadow hull;
finite prime-degree defect tower;
defect multiplicativity and prime-layer detection;
defectless projection escape;
Abhyankar local-uniformization route;
purely inseparable alteration route;
dependent/independent prime-defect classification;
finite differential-ramification portfolio;
finite uniformizing alteration portfolio;
shadow-octahedron for finite prime towers;
Noetherian ACC for genuinely new coherent alteration shadows;
X045 coherent recurrent termination.
```

### Remaining load-bearing chain

```text
INDEPENDENT-DEFECT EFFECTIVITY (IDE)
-> UDE-EV
-> NO EQUAL-OR-HIGHER CLASS-V BIRTH
-> STRICT CLASS-V ORDINAL
-> FULL GLOBAL SOURCE-CAUSAL TERMINATION
-> FINITE ZARISKI/ETALE SERIALIZATION
-> PRINCIPALIZATION AND FUNCTORIAL RESOLUTION.
```

---

## 11. Truth boundary

```text
FINITE_SHADOW_HULL                              = standard/finite construction
PRIME_DEFECT_TOWER_REDUCTION                    = standard valuation theory
DEPENDENT_DEFECT_CLASSIFICATION                 = standard valuation theory
DEFECTLESS_AND_ABHYANKAR_ROUTES                 = external positive theorems
FINITE_EXTENSION_OR_INSEPARABLE_UNIFORMIZATION  = external positive theorems
ALTERATION_SHADOW_COMPLEX                       = finite candidate construction
VISIBLE_SHADOW_ACC                              = conditional finite-type theorem
INDEPENDENT_DEFECT_EFFECTIVITY                   = open
UNIFORM_EVENT_VISIBLE_DEFECT_ESCAPE             = open conditional on IDE
STRICT_CLASS_V_ORDINAL                          = open
GLOBAL_TERMINATION                              = open
FINITE_FUNCTORIAL_GLOBALIZATION                 = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION      = not established
```

The highest-information next target is IDE: prove that a stable independent-defect packet visible to the complete finite state produces an effective coherent alteration shadow on the original model, or prove exact descent from the monomial uniformizing alteration.
