# MLEL-X048 / FDI-RRF-NNW-FINAL

## Finite-Flat Descent Intervals, the Ramification-Residue Firewall, and Norm--Newton Wild Preparation
## 有限平坦下降区间、分歧剩余防火墙与 Norm--Newton 野准备

**Parents:** MLEL-X047 / WAD-GCD-UWP-FINAL; MLEL-X046 / PDS-AST-IDE-FINAL; MLEL-X044 / COP-PCH-UCS-FINAL; MLEL-X042--X043 transform and legality line.  
**Date:** 2026-08-05  
**Class:** exact finite-flat ideal descent algebra + codimension-one non-descent theorem + toroidal norm--Newton base-first preparation.  
**Global status:** `OPEN_GAP`.

---

## 0. Executive verdict

X047 proved the exact statement

```text
zero complete Cech--Rees shadow -> effective descent of the upper word.
```

It left open the construction of an upper regular word whose complete shadow is zero or strictly lowerable. X048 shows that this target, when interpreted as descent of an arbitrary regular upper monomial word, is too strong in the presence of ramification.

1. For a finite faithfully flat algebra `A->B` and a finite ideal `J subset B`, there are canonical extremal base ideals

   ```text
   I_-(J)=Ann_A(B/J),
   I_+(J)=image(B^dual tensor_A J -> A).
   ```

   They satisfy

   ```text
   I_-(J)B subset J subset I_+(J)B.
   ```

   `I_-` is the largest descended ideal whose extension lies in `J`; `I_+` is the smallest descended ideal whose extension contains `J`. The ideal `J` descends if and only if `I_-=I_+`.

2. At a codimension-one ramified point, the exponent vector of an invertible upper ideal has a residue modulo the ramification indices. A base ideal pulls back with exponents `e_i a`. If the upper exponents are not of this form, the ideal does not descend, and no sequence of ordinary base blowups can repair the discrepancy at the generic point of that divisor. This is the **ramification-residue firewall**.

3. Consequently, an upper regular centre may be alteration-only. The model `t=s^e` and the upper centre `(s)` is the sharp example: `(s)` is regular but does not descend, while the blowup of the downstairs Cartier divisor `(t)` is the identity. X047 zero-shadow descent remains correct but cannot be the universal route to wild preparation.

4. The correct universal strategy is base-first. In a diagonal toroidal finite-flat chart

   ```text
   x_i=u_i^(e_i),   n=product_i e_i,
   ```

   and for an upper monomial ideal `J=(u^(alpha_1),...,u^(alpha_m))`, define the norm--Newton ideal on the base by the monomials

   ```text
   x^(beta_a),    beta_(a,i)=n alpha_(a,i)/e_i.
   ```

   Its pullback has Newton polyhedron `n NP(J)`. Hence

   ```text
   integralClosure(NN_f(J) O_Y)=integralClosure(J^n),
   ```

   and the normalized blowups have the same toric fan after base change.

5. A regular refinement of the base Newton fan is realized by a finite characteristic-free sequence of ordinary blowups in regular toroidal strata. After normalized pullback, this base word principalizes the upper monomial ideal. The upper regular centres need not descend, and no weighted or stacky modification is used on the base.

6. For a finite marked family, first form the X044 exact joint marked sum and then apply the norm--Newton construction. This gives one base monomial modification which treats all active colours simultaneously. Tor--Valabrega, source, contact, differential-ramification, and Cech discrepancies remain separate colours.

7. The X047 single target is therefore superseded. The new target is **Ramification-Balanced Base-First Wild Preparation (RB-BFWP)**:

   ```text
   toroidalize the finite wild shadow map;
   form the base norm--Newton/joint-shadow ideal;
   realize its regular toroidal refinement by ordinary base blowups;
   compare the normalized pullback with the complete upper packet;
   obtain either terminal monomiality, an earlier valuation drop,
   or a nonzero coherent shadow strictly reduced downstairs.
   ```

The remaining difficulty is no longer descent of an arbitrary upper word. It is the effectivity and strict shadow reduction of the base-first norm--Newton modification for a general independent Artin--Schreier packet. General arbitrary-dimensional positive-characteristic resolution remains open.

---

## 1. Extremal ideals for finite-flat descent

Let `A->B` be finite faithfully flat and of finite presentation. Let `J subset B` be a finitely generated ideal. Write `B^dual=Hom_A(B,A)`.

### Definition 1.1 -- lower and upper descent ideals

Define

```text
I_-(J)=Ann_A(B/J)
      ={a in A | aB subset J},
```

and

```text
I_+(J)=image(B^dual tensor_A J -> A),
```

where the map is evaluation.

### Theorem 1.2 -- finite-flat descent interval

The following hold.

1. `I_-(J)B subset J subset I_+(J)B`.
2. If `IB subset J`, then `I subset I_-(J)`.
3. If `J subset IB`, then `I_+(J) subset I`.
4. The ideal `J` is extended from `A` if and only if `I_-(J)=I_+(J)`.
5. In that case the unique descended ideal is their common value.

### Proof

The first inclusion for `I_-` is the definition. For the upper inclusion, work locally where `B` is free with dual bases `{e_i}` and `{phi_i}`. Every `j in J` has

```text
j=sum_i phi_i(j)e_i,
```

and every coefficient lies in `I_+(J)`. The extremal assertions are immediate from the definitions.

If `J=IB`, faithful flatness gives `Ann_A(B/IB)=I`. Locally the element `1 in B` is unimodular and extends to a basis, so there is `phi in B^dual` with `phi(1)=1`; hence `I subset I_+(IB)`. The opposite inclusion follows from extremality, and therefore `I_-=I_+=I`.

Conversely, if `I_-=I_+=I`, the two inclusions in (1) give `J=IB`.

### Definition 1.3 -- descent gap

The finite descent gap is

```text
Gap_f(J)=J/I_-(J)B  directSum  I_+(J)B/J.
```

It vanishes exactly when `J` descends. The exactified packet also retains `B/J`, the evaluation map, and both inclusions, because annihilators and images must be transported through nonflat preparatory blowups by the X042 universal-exactification mechanism.

---

## 2. Codimension-one ramification residue

Let `A` be a DVR with uniformizer `t`, and let `B` be the semilocal normalization in a finite extension, with branches `B_j`, uniformizers `u_j`, and

```text
t = epsilon_j u_j^(e_j).
```

Let an invertible upper ideal have factorization

```text
J=product_j (u_j)^(d_j).
```

### Theorem 2.1 -- ramification-balance criterion

The ideal `J` is extended from `A` if and only if there is an integer `a>=0` such that

```text
d_j=e_j a
```

for every branch `j`.

### Proof

Every nonzero ideal of `A` is `(t^a)`. Its extension has valuation `e_j a` in `B_j`. Conversely, equality of the exponent vectors gives equality of the invertible ideals.

### Definition 2.2 -- divisorial residue

The ramification residue of `J` at the base divisor is the class of `(d_j)_j` modulo the diagonal ramification lattice

```text
{(e_j a)_j | a in Z}.
```

### Theorem 2.3 -- ramification-residue firewall

Let `X` be regular and normal, and let `Y->X` be finite flat near the generic point of a divisor `E subset X`. If an invertible upper ideal has nonzero ramification residue over `E`, then no finite sequence of ordinary blowups of `X` makes its strict transform descend in a neighbourhood of the generic point of `E`.

### Proof

A proper birational morphism between normal schemes is an isomorphism at the generic point of a codimension-one divisor; an attempted blowup in the divisor itself is the identity. Hence the extension of DVRs and the exponent vector are unchanged at that point. The criterion of Theorem 2.1 continues to fail.

### Counterexample 2.4

For `A=k[t]`, `B=k[s]`, `t=s^e`, the regular upper Cartier ideal `(s)` has residue `1 mod e` and does not descend. The lower and upper descent ideals are

```text
I_-=(t),
I_+=A.
```

The base blowup in `(t)` is the identity. Thus a nonzero Cech shadow need not be lowerable by trying to force the same upper centre to descend.

---

## 3. The correction to wild groupoid preparation

The ramification firewall implies three rules.

1. An arbitrary regular centre selected on a wild cover is not a legitimate candidate for stagewise descent.
2. A nonzero descent gap supported generically on a ramification divisor is not a lower-dimensional defect; it is a proof that the upper centre belongs only to the alteration.
3. The base algorithm must construct its own centre from a coherent shadow. The upper cover is diagnostic and need only become compatible after normalized common refinement.

The X047 zero-shadow theorem remains the exact clean chamber. The universal branch, however, must be base-first rather than upper-word-first.

---

## 4. Norm--Newton ideal in the diagonal toroidal chamber

Let

```text
A=k[x_1,...,x_r],
B=k[u_1,...,u_r],
x_i=u_i^(e_i),
n=product_i e_i,
```

localized or completed at the toroidal origin. Let

```text
J=(u^(alpha_1),...,u^(alpha_m))
```

be a monomial ideal, with `alpha_a in N^r`.

### Definition 4.1 -- norm--Newton ideal

For each generator define

```text
beta_(a,i)=n alpha_(a,i)/e_i.
```

This is integral because `e_i` divides `n`. Set

```text
NN_f(J)=integralClosure((x^(beta_1),...,x^(beta_m))) subset A.
```

Equivalently, the displayed monomials are the field norms of the generators up to units. The integral closure makes the construction depend only on the Newton polyhedron of `J`, not on a chosen generating set.

### Theorem 4.2 -- Newton pullback identity

The extended norm--Newton ideal satisfies

```text
integralClosure(NN_f(J)B)=integralClosure(J^n).
```

### Proof

The pullback of `x^(beta_a)` is

```text
u_1^(e_1 beta_(a,1)) ... u_r^(e_r beta_(a,r))=u^(n alpha_a).
```

Therefore the Newton polyhedron of the extended ideal is

```text
conv{n alpha_a}+R_{≥0}^r=n NP(J).
```

The Newton polyhedron of `J^n` is also `n NP(J)`. Integral closure of a monomial ideal consists precisely of the monomials whose exponent vectors lie in its Newton polyhedron.

### Corollary 4.3 -- normalized blowup comparison

The normalization of the pullback of `Bl_(NN_f(J))(Spec A)` has the same toric fan as the normalized blowup of `J` on `Spec B`. Powers and integral closure do not change the normalized blowup.

### Proof

The normalized blowup of a monomial ideal is the toric modification defined by the normal fan of its Newton polyhedron. Scaling a polyhedron by `n` does not change the normal fan. Apply Theorem 4.2.

---

## 5. Base-first ordinary toroidal word

### Theorem 5.1 -- diagonal base-first monomialization

In the setting of Section 4 there is a finite sequence of ordinary blowups of `Spec A` in regular toroidal strata such that:

1. the sequence dominates the normalized blowup of `NN_f(J)`;
2. the transformed norm--Newton ideal is invertible and monomial;
3. after base change to `B` and normalization, the transform of `J` is invertible and monomial;
4. the construction is characteristic-free and allows `p` to divide some `e_i`.

### Proof

Take a regular subdivision of the common Newton fan. Since the ambient toroidal cone is regular, a finite sequence of star subdivisions and barycentric refinements realizes it by ordinary blowups in regular invariant strata. The pullback fan in the lattice of `B` is the same rational fan; after saturation/normalization it principalizes `J` by Corollary 4.3.

### Boundary

The normalized pullback is a comparison space, not the final resolution. The final modification on the original model is the ordinary base word. The difference between the ordinary pullback and its normalization is retained in the X046 differential-ramification and X047 Cech-Rees shadow portfolio.

---

## 6. Finite marked families

Let `{(J_lambda,b_lambda)}` be finitely many upper monomial marked ideals. Choose a common multiple `B_0` of the marks and form the exact joint marked ideal

```text
J_joint=sum_lambda J_lambda^(B_0/b_lambda).
```

For a regular upper centre, permissibility for `(J_joint,B_0)` is equivalent to permissibility for every colour. Define the base shadow ideal

```text
NN_f(J_joint).
```

### Proposition 6.1 -- simultaneous norm--Newton preparation

A regular toroidal refinement of `NN_f(J_joint)` gives one base ordinary word whose normalized pullback principalizes all active upper colours simultaneously. Passive, source, boundary, contact, and differential-ramification data remain separate colours and are prepared by the complete X044 portfolio.

### Proof

The joint marked sum commutes with controlled transform. Its Newton polyhedron is the convex hull of the scaled coloured polyhedra. Theorem 5.1 principalizes the joint ideal. Exact marked aggregation then gives simultaneous active permissibility. The remaining conditions are not inferred from the aggregate and are carried separately.

---

## 7. The descent-gap/support dichotomy

For a monomial upper ideal `J`, compute its divisorial ramification residues.

```text
UNBALANCED DIVISORIAL BRANCH:
  some residue is nonzero;
  the upper ideal is alteration-only and is not used as a candidate centre;
  replace it by the base norm--Newton shadow.

BALANCED BRANCH:
  all codimension-one residues vanish;
  the descent gap Gap_f(J) is supported in codimension at least two;
  exactify the gap and enroll its Fitting/support layers in the X044
  lower-dimensional actual-centre portfolio.
```

The balanced branch may eventually enter the X047 zero-shadow chamber. The unbalanced branch is handled only by base-first shadow preparation.

---

## 8. Corrected single target

### Ramification-Balanced Base-First Wild Preparation (RB-BFWP)

For one independent Artin--Schreier degree-`p` layer, after finite-flat and toroidal preparation, construct on the base a finite norm--Rees/Newton shadow portfolio such that one finite ordinary regular base word has, uniformly on the valuation neighbourhood, one of the following outcomes:

1. the normalized pullback monomializes the complete upper event-visible packet and all remaining shadows vanish;
2. a nonzero balanced codimension-at-least-two descent gap or differential/Cech shadow is produced and strictly lowered by the X044 block on every chart;
3. effective key degree, conductor height, support dimension, radicial exponent, prime-layer profile, or common-model class strictly drops.

The theorem must preserve immutable valuation and source ancestry and must forbid equal-or-higher class-V birth.

### Minimal proof cut

```text
RBFW-1  toroidalization of the finite event-visible wild map;
RBFW-2  global norm--Rees/Newton shadow independent of local diagonal charts;
RBFW-3  ordinary regular base refinement of the norm shadow;
RBFW-4  exact normalized-pullback comparison for the complete packet;
RBFW-5  strict reduction of every balanced residual shadow;
RBFW-6  common-refinement and smooth/etale compatibility;
RBFW-7  no equal-or-higher class-V birth.
```

---

## 9. Candidate-graph contraction

### Closed or reduced after X048

```text
finite-flat lower/upper descent ideals and exact descent criterion;
finite descent-gap packet;
codimension-one ramification-balance theorem;
ramification-residue persistence under base blowups;
no-go for universal descent of arbitrary upper regular centres;
diagonal norm--Newton pullback identity;
normalized blowup comparison in the monomial chamber;
base-first ordinary toroidal monomialization in the diagonal chamber;
simultaneous marked norm--Newton preparation;
X047 zero-shadow descent as the clean branch.
```

### Remaining chain

```text
RB-BFWP
-> UDE-EV
-> no equal-or-higher class-V birth
-> strict class-V ordinal
-> full global source-causal termination
-> finite Zariski/etale serialization
-> principalization and functorial resolution.
```

---

## 10. Truth boundary

```text
FINITE_FLAT_DESCENT_INTERVAL                     = closed
RAMIFICATION_BALANCE_AT_CODIMENSION_ONE          = closed
RAMIFICATION_RESIDUE_FIREWALL                     = closed
ARBITRARY_UPPER_WORD_DESCENT_UNIVERSAL            = false
DIAGONAL_MONOMIAL_NORM_NEWTON_THEOREM             = closed
DIAGONAL_BASE_FIRST_TOROIDAL_PREPARATION          = closed
GLOBAL_NORM_REES_SHADOW                           = open
GENERAL_WILD_TOROIDALIZATION                      = open
BALANCED_SHADOW_STRICT_REDUCTION                  = open
RB_BFWP                                            = open
UDE_EV_AND_CLASS_V_ORDINAL                         = open
GLOBAL_TERMINATION_AND_GLOBALIZATION               = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = not established
```

X048 removes a structural overreach from X047. The zero-shadow descent theorem remains valid, but universal wild preparation must not be formulated as descent of arbitrary regular centres chosen upstairs. The most likely route is a base-first norm--Newton modification, with the alteration used only to compute and verify the shadow.
