# MLEL-X054 Supplement

## Radicial Root Uniformization and Frobenius Transfer

### 1. Local equation and cleaning

Let `A` be excellent regular local with an ordered SNC boundary and let `K'=K(z)`, `z^p=a`. Multiplication and translation put the normalization locally into the form `A[z]/(z^p-a)` with `a` `p`-clean in the completed logarithmic graded ring. Cleaning is a presentation change, not a geometric step, and retains the exceptional-history label.

### 2. Intrinsic state

The finite state consists of the logarithmic differential support, normal Hasse coefficients, projective residual-contact ideal, first active Frobenius layer, differential/Fitting presentation, and aged exceptional history. All objects are coherent and commute with smooth/etale base change.

### 3. Chart calculation

On a blowup chart with exceptional equation `x`, divide the total transform by the largest absorbable `p`th power. With `q=floor(m/p)`:

```text
z=x^q z',
a'=x^(-pq)a^tot.
```

The transformed logarithmic differential detects exponents not divisible by `p`. If the support is regular, projective contact lowers by one. If the exceptional exponent is divisible by `p`, Cartier/Hasse cleaning exposes a lower active Frobenius layer. A reappearing old exceptional contribution has a strictly lower aged-history multiset.

### 4. Termination

The lexicographic state

```text
(dim support, projective contact height,
 Frobenius level, Fitting profile, aged history)
```

is well founded. Every nonterminal chart lowers it. Terminal equations are logarithmically monomial. Their saturated cone is a finite rational toric cone; a regular subdivision gives ordinary blowups in regular boundary strata.

### 5. Frobenius transfer

After iterating degree-`p` layers to obtain a regular centre on `F^(1/p^e)`, take etale parameters `u_i` and set `t_i=u_i^(p^e)`. The Frobenius field isomorphism transfers the finite unramified henselian branch to a finite separable defectless branch of `F/k(t)`.

### 6. Interfaces used

- X035/X044: support-thickness and complete actual-centre synthesis;
- X042/X043: exactified transform, normal-jet legality, all-chart reentry;
- X045: no-rebirth/source multiset descent;
- X053: Riemann-Zariski finite atlas and hereditary regular common refinement.