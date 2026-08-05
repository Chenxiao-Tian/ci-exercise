# MLEL-X044 Supplement

## Monomial Face Complexes and Source-Closed Toroidal Centre Blocks

**Parent:** `MLEL-X044 / COP-PCH-UCS-FINAL`  
**Date:** 2026-08-05  
**Status:** characteristic-free toroidal compiler; global recurrent termination remains open.

---

## 1. Monomial face data

Let `(W,E)` be regular with ordered SNC boundary

```text
E=H_1+...+H_s.
```

A finite coloured marked portfolio is locally

```text
I_lambda=O(-sum_i a_(lambda,i)H_i),
mark b_lambda.
```

For a face `S`, set

```text
ord_S(lambda)=sum_(i in S)a_(lambda,i).
```

The face is jointly admissible when `ord_S(lambda)>=b_lambda` for every active colour. The admissible set is upward closed. Intersections correspond to unions of faces and remain admissible.

## 2. Existence without a selector

At a nonterminal point, the full set of boundary components through the point is admissible. Hence the finite admissible-face complex is nonempty. Blow all deepest faces at once. They are pairwise disjoint, so their union is one actual regular centre. The construction is invariant under automorphisms preserving the coloured exponent matrix.

## 3. Transform formula

For a centre face `S` and a pivot `j in S`, the controlled transform has new exceptional exponent

```text
sum_(i in S)a_(lambda,i)-b_lambda,
```

which is nonnegative. The remaining exponents are the standard star-subdivision transforms, so every successor stays in the category of finite coloured monomial marked portfolios.

## 4. Finite toroidal word

Take the common Newton fan of all colours and marks and a canonical regular refinement by finitely many star subdivisions. Each subdivision is realized by an ordinary blowup of a regular boundary stratum. On the refined fan every Newton support function is linear; subsequent deepest-face blowups clear the marked singular locus. The word is finite.

## 5. Thickness

Top graded pieces and Hasse/Fitting coefficient ideals of a nilpotent contact packet are additional colours. After simultaneous monomialization their Newton polyhedra enter the same common fan. A separate selector for maximal thickness is unnecessary. The toroidal subdivision height decreases, and tangent models recover the contact change `m -> m-1`.

## 6. Source labels

Every intersection and face label is a union of finitely many incoming source labels. One block therefore has only finitely many internal source identities and creates no free birth. New successor sources must be represented by coherent event cohomology.

## 7. Boundaries

- Uncoloured product aggregation loses owners and marks.
- Radical principalization loses nilpotent thickness.
- Flatifying only defect modules loses kernel/image formation; the exactified X042 diagram remains enrolled.
- Stacky or weighted toroidal modifications are not permitted final outputs; each subdivision is an ordinary blowup in a regular stratum.
- Finite source closure of one block does not imply global termination of successor blocks.
