# MLEL-X047 / FCD-RAE-ZSD-FINAL

## Finite-Flat Cech Descent, Rees-Algebra Effectivity, and the Zero-Shadow Theorem
## 有限平坦 Cech 下降、Rees 代数有效性与零影子定理

**Parents:** MLEL-X046 / PDS-AST-IDE-FINAL; MLEL-X045 / AEF-NUB-CRX-FINAL; MLEL-X044 / COP-PCH-UCS-FINAL; MLEL-X042--X043 transform and legality line.  
**Date:** 2026-08-05  
**Class:** standard finite-flat descent closure + finite Cech-Rees obstruction packet + single wild-layer zero-shadow theorem.  
**Global status:** `OPEN_GAP`.

---

## 0. Executive verdict

X046 isolated **Independent-Defect Effectivity (IDE)** and correctly identified zero-shadow descent as the smallest decisive case. Its shadow portfolio, however, still omitted one indispensable datum: descent is not determined by traces, differentials, conductors, Fitting ideals, or invariance under a finite group. It is determined by a Cech descent datum on the finite-flat relation.

X047 makes this correction and closes the zero-shadow side of IDE in the first genuine wild chamber.

1. A proper generically finite alteration which is finite locally free on the good open becomes finite locally free after a good-open-admissible blowup of the base. The X044 actual-centre theorem is the conditional regular-centre realization of that flattening modification.
2. On the resulting finite faithfully flat cover `f:Y->X`, the complete upper object is enlarged from a differential-ramification shadow to a **Cech-Rees object**: the bounded coloured complex, all ideal inclusions, all graded Rees algebras, multiplication maps, owner/source labels, and terminal certificates are compared on `Y x_X Y`, and the cocycle is compared on `Y x_X Y x_X Y`.
3. The first comparison cone, the cocycle cone, and the structure-map cones form a finite coherent Cech-Rees shadow downstairs. A nonzero shadow is an effective coherent obstruction on the original model.
4. If the complete Cech-Rees shadow is zero, fpqc descent is effective. The upper modules, ideals, graded Rees algebras, and centre word descend uniquely. Blowup commutes with flat base change; quasi-regular immersion, regularity, flatness, marked containments, and the exact conormal/logarithmic certificates descend. Thus a zero-shadow upper ordinary centre word gives an ordinary regular jointly legal centre word on the base.
5. Consequently the X046 implication

   ```text
   all typed shadows vanish -> upper monomial packet descends
   ```

   is valid only after “typed shadows” includes the complete Cech-Rees descent shadow. With that correction, the implication is a theorem.
6. For one independent Artin--Schreier degree-p layer, after finite-flat preparation and exactification, there is an exhaustive dichotomy:

   ```text
   nonzero Cech-Rees shadow
       -> coherent Fitting/support colour on the base;

   zero Cech-Rees shadow
       -> exact stagewise descent of the upper ordinary centre word.
   ```

7. The remaining single target is no longer zero-shadow descent. It is **Cech-Compatible Wild Monomialization (CCWM)**: construct, on a finite uniformizing wild cover, a finite ordinary centre word for the complete event-visible packet whose full Cech-Rees discrepancy is either nonzero and strictly lowerable downstairs or zero.

General arbitrary-dimensional positive-characteristic resolution is not established.

---

## 1. Why X046 needed a Cech correction

Let `A=k[t]`, `B=k[s]`, and `t=s^2` in characteristic different from two. The finite flat morphism `Spec B -> Spec A` is ramified. The ideal `(s)` is stable under the involution `s -> -s`, but it does not descend from an ideal of `A`: every principal ideal pulled back from the local parameter `t` has even `s`-adic order. Thus group stability does not supply fpqc descent on a ramified cover.

The same defect appears in a wild finite cover. An upper monomial ideal may be stable under every visible automorphism and still fail the equalizer condition on the full relation `Y x_X Y`. Therefore the complete descent datum must be retained.

The correct zero-shadow statement is not

```text
trace, differential and ramification shadows vanish;
```

but

```text
all typed prime-layer shadows vanish,
and the complete Cech-Rees descent datum is effective.
```

---

## 2. Finite-flat preparation of the alteration

Let `f:Y->X` be a proper generically finite chart in the X046 uniformizing portfolio. Let `U subset X` be the quasi-compact good open on which `f` is finite locally free and the event-visible packet is already in the required chamber.

### Theorem 2.1 -- finite-flat preparation

There is a `U`-admissible blowup `pi:X'->X` such that the strict transform

```text
f':Y'->X'
```

is finite locally free. If `U` meets every component, `f'` is finite faithfully flat on the relevant support.

### Proof

Apply flattening by blowup to the proper morphism. Once the strict transform is flat and finitely presented, properness and finiteness over the schematically dense good open imply finiteness; finite flat of finite presentation is finite locally free. Restrict to the union of components met by the valuation neighbourhood to obtain faithful flatness.

### Geometric realization

The flattening centre need not be regular. In the resolution programme it is represented by its centre-exact modification ideal and passed to the X044 complete coloured portfolio. Conditional on the lower-dimensional full-portfolio theorem, that modification is realized by a finite word of ordinary blowups in regular jointly legal centres. The finite-flat strict transform is unchanged after passing to a common centre-exact refinement.

---

## 3. The complete Cech-Rees shadow

Let `f:Y->X` now be finite faithfully flat. Set

```text
Y^[2]=Y x_X Y,
Y^[3]=Y x_X Y x_X Y.
```

Write `p_0,p_1:Y^[2]->Y` and `p_01,p_12,p_02:Y^[3]->Y^[2]` for the projections.

Let `Q_Y` denote the complete prepared upper object. It contains:

```text
a bounded coherent coloured complex;
all owner modules and active marked ideals;
all ideal embeddings into the structure sheaf;
all graded Rees algebras and multiplication maps;
source, boundary, contact and history filtrations;
the finite centre word and its stagewise centre ideals;
the terminal regularity and SNC certificates.
```

A proposed descent datum is a comparison

```text
phi:p_0^*Q_Y -> p_1^*Q_Y
```

on `Y^[2]`, compatible with every displayed structure map.

### Definition 3.1 -- Cech-Rees shadow

The Cech-Rees shadow is the finite direct sum of the following bounded coherent defects, pushed forward to `X`:

1. the cone of `phi` and the cone of a chosen inverse comparison;
2. the cocycle cone comparing

   ```text
   p_12^*phi o p_01^*phi
   ```

   with `p_02^*phi` on `Y^[3]`;
3. the cones measuring compatibility with ideal embeddings, Rees multiplication, grading, owner/source filtrations, boundary incidence, and the stagewise centre maps;
4. the corresponding cohomology Fitting layers.

Because `f`, `Y^[2]->X`, and `Y^[3]->X` are finite, every pushed-forward term is coherent. The shadow is finite: quasi-coherent descent is controlled by one comparison and its cocycle, while all algebraic structures in `Q_Y` are finitely presented.

### Proposition 3.2 -- first nonzero layer is effective

If the Cech-Rees shadow is nonzero, its first nonzero cohomology/Fitting layer is a nonzero coherent colour on the original finite model. It is supported away from the good open and can be enrolled in the X044 actual-centre portfolio.

### Proof

Finite pushforward is exact on quasi-coherent modules and preserves coherence. A nonzero finite module remains nonzero after finite pushforward. The intrinsic Fitting filtration gives a choice-free proper closed support.

---

## 4. Zero-shadow exact descent

### Theorem 4.1 -- zero-shadow descent for a complete coloured object

Assume the complete Cech-Rees shadow of `Q_Y` is zero. Then there is a unique complete coloured object `Q_X` on `X` whose pullback is `Q_Y`. In particular:

1. every upper coherent module descends;
2. every upper ideal and its embedding into `O_Y` descend to an ideal of `O_X`;
3. every finite graded Rees algebra descends as a graded `O_X`-algebra;
4. all multiplication, Hasse, Fitting, source, owner, boundary, and history maps descend;
5. the descended data are compatible with open restriction and further flat base change.

### Proof

Vanishing of the comparison and cocycle defects gives an fpqc descent datum on each coherent module and on every morphism between them. Effectivity and full faithfulness of fpqc descent yield the unique downstairs modules and maps. The descended map from an ideal to `O_X` is injective because its pullback is injective and `f` is faithfully flat. Algebra multiplication, unit, grading, and the Rees relations descend by full faithfulness.

### Corollary 4.2 -- descent of one centre

Let `J_Y subset O_Y` be a finitely generated centre ideal occurring in `Q_Y`. If its complete Cech-Rees shadow is zero, there is a unique finitely generated ideal `J_X subset O_X` with

```text
J_X O_Y = J_Y.
```

Moreover

```text
Bl_(J_Y)(Y) = Bl_(J_X)(X) x_X Y.
```

If `J_Y` is a quasi-regular centre, then `J_X` is quasi-regular. If the upper centre and the finite-flat cover are of finite presentation and the upper centre is regular, then the descended centre is regular.

### Proof

The ideal descends by Theorem 4.1. The Rees algebra descends and relative Proj commutes with flat base change, giving the blowup identity. Quasi-regular immersion is fpqc local on the base. Regularity descends through faithfully flat finitely presented morphisms.

---

## 5. Stagewise descent of an ordinary centre word

Consider an upper word

```text
Y_m -> Y_(m-1) -> ... -> Y_0=Y
```

of ordinary blowups in finitely generated ideals `J_(i,Y)`. Suppose the complete stagewise Cech-Rees shadow is zero.

### Theorem 5.1 -- centre-word effectivity

There is a unique word

```text
X_m -> X_(m-1) -> ... -> X_0=X
```

of ordinary blowups such that

```text
Y_i = X_i x_X Y
```

for every `i`, and the upper centre at stage `i` is the pullback of the downstairs centre. If the upper word consists of regular centres, then so does the downstairs word.

If the complete X043 legality packet has zero Cech shadow, the descended word is jointly active-permissible, passive/Tor-safe, logarithmically compatible, source conservative, and centre exact.

### Proof

Descend the first centre by Corollary 4.2. Blowup commutes with flat base change, so the first upper successor is the pullback of the descended successor and remains finite faithfully flat over it. Apply the same argument inductively. Regularity and quasi-regularity descend fpqc. Marked containments descend by faithful flatness; flatness and exactness descend fpqc; the normal-jet and logarithmic certificates descend because all defining finite modules and maps are included in the complete Cech-Rees object.

### Corollary 5.2 -- terminal certificate descent

If the upper word terminates in a regular strict transform with SNC total boundary and the terminal certificate has zero Cech shadow, then the corresponding downstairs strict transform is regular with SNC total boundary.

---

## 6. The independent Artin--Schreier one-layer theorem

Let `(L|K,v)` be one independent Artin--Schreier defect layer of degree `p`, and let `Y->X` be one finite alteration model carrying the complete event-visible shadow hull. Perform the finite-flat preparation of Section 2 and exactify all typed comparisons.

### Theorem 6.1 -- one-layer zero-shadow dichotomy

For any finite ordinary upper centre word prepared for the complete event-visible packet, exactly one of the following occurs after a finite constructible refinement of the valuation neighbourhood:

1. the complete Cech-Rees shadow is nonzero; then its first nonzero Fitting layer is a coherent effective shadow on the original model;
2. the complete Cech-Rees shadow is zero; then the entire upper centre word and terminal packet descend exactly to an ordinary regular jointly legal word on the original model.

### Proof

The Cech-Rees shadow is a finite coherent object. Either it is zero or it is not. In the second case use Proposition 3.2. In the first case apply Theorems 4.1 and 5.1. The constructible refinement makes the finite presentations and ranks constant.

### Consequence for IDE

The zero-shadow clause of X046 IDE is now proved for one independent Artin--Schreier layer, provided the upper word is finite and the complete Cech-Rees packet has been formed. No appeal to an unspecified “effective trace descent” remains.

---

## 7. Finite wild towers

A finite tame-wild tower has finitely many cyclic degree-`p` and radicial layers. Form the layerwise Cech-Rees shadow together with the typed differential-ramification shadow.

### Theorem 7.1 -- tower shadow filtration

The complete shadow of the finite tower has a finite filtration whose graded factors are the transported one-layer typed shadows and one-layer Cech-Rees shadows. If every graded factor vanishes, the entire upper centre word descends stagewise. If some factor is nonzero, the first nonzero factor yields a coherent effective colour on the corresponding lower model.

### Proof

Compose the layer comparisons and the descent comparisons, and apply the X045 octahedral filtration. The word is finite, so the filtration is finite. Apply Theorem 6.1 to the first nonzero layer or descend inductively when the factor is zero.

---

## 8. Candidate-graph contraction

### Closed or reduced to standard inputs after X047

```text
finite-flat preparation of a proper alteration;
finite Cech-Rees shadow on the 2-truncated nerve;
coherent effectivity of the first nonzero Cech layer;
fpqc descent of complete coherent packets;
descent of ideals and finite graded Rees algebras;
flat-base-change identity for blowups;
fpqc descent of quasi-regular and regular centres;
stagewise descent of a zero-shadow ordinary centre word;
zero-shadow exact descent for one independent Artin--Schreier layer;
finite wild-tower compilation by the event octahedron.
```

### Corrected remaining chain

```text
Cech-Compatible Wild Monomialization (CCWM)
-> strict reduction of every nonzero Cech/differential shadow
-> finite upper word for every class-V neighbourhood
-> UDE-EV
-> strict class-V ordinal
-> full global source-causal termination
-> finite Zariski/etale serialization
-> principalization and functorial resolution.
```

### Highest-information next target

> **CCWM.** On the finite-flat preparation of one independent Artin--Schreier layer, construct a finite ordinary word which monomializes the complete event-visible packet and whose complete Cech-Rees shadow is either zero or has a first nonzero layer strictly lowered by the descended X044 block on every valuation and chart.

---

## 9. Truth boundary

```text
FINITE_FLAT_PREPARATION                           = standard closed input
CECH_REES_SHADOW_FINITE_COHERENT                  = closed construction
FIRST_NONZERO_CECH_LAYER_EFFECTIVE                = closed
ZERO_SHADOW_FPQC_DESCENT                          = standard closed
IDE_ZERO_SHADOW_SINGLE_AS_LAYER                   = closed in the stated chamber
FINITE_TOWER_ZERO_SHADOW_COMPILATION              = closed conditional on layer words
CECH_COMPATIBLE_WILD_MONOMIALIZATION              = open
UNIFORM_IMMEDIATE_DEFECT_ESCAPE                    = open
STRICT_CLASS_V_ORDINAL                             = open
GLOBAL_TERMINATION_AND_GLOBALIZATION               = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = not established
```

X047 removes a genuine logical gap from X046: zero differential-ramification shadow is not enough, but zero **complete Cech-Rees shadow** is enough. The remaining difficulty is now the construction and strict reduction of a Cech-compatible upper wild word, not the descent theorem itself.
