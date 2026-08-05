# MLEL-X042 / RFG-TVC

## Regular-Flag Graded Comparison, Tor-Valabrega Closure, and Terminal Source Realization
## 正则旗标分次比较、Tor-Valabrega 闭合与终端来源实现

**Parents:** MLEL-X038 / TVF-ANC; MLEL-X039 / NTR-RFL; MLEL-X040 / CFT-ACN; MLEL-X041 / HNC-STC-RFL; MLEL-X041 / CEW-SNR  
**Date:** 2026-08-05  
**Class:** standard scheme-theoretic closure plus exactified candidate-graph concentration  
**Global status:** OPEN_GAP

---

## 0. Executive verdict

X042 concentrates the transform side of the programme on one finite coherent object. For a nested regular flag `D ⊂ C ⊂ W`, the comparison between the old normal module and the normal module of the ambient strict transform factors canonically through the image filtration. The exact defects are:

1. the Tor/filtration-base-change kernel;
2. the Valabrega intersection kernel;
3. the saturation-generation cokernel.

Their all-degree, all-owner direct sum is finite over a two-ideal mixed-Rees algebra. Homogenization produces one proper coherent packet on `P_C(O_C ⊕ I_C/I_C²)`. To make the flat-kill step stable under the nonflat preparation, X042 retains the complete exactified diagram: all sources, targets, kernels, images, cokernels, and multiplication-image sequences. Admissible flatification makes every member flat. The resulting short exact sequences are then universally exact, while the three generically-zero defect modules vanish on the reduced carrier by flat-kill. This closes the carrier-side comparison on a fixed centre-exact mixed-Rees chart. The identification of this prepared chart complex with the successor ambient comparison remains part of ambient regular trace realization.

The X041 CEW-SNR correction is retained: a finite centre-exact word of ordinary blowups has no terminal exceptional recharge. Composition of blowups and composition of strict transforms make the terminal transform fully saturated for the composite centre. Recharge is therefore not a fourth independent regular-flag defect.

The remaining decisive geometric interface is ambient regular trace realization: the carrier flatifier and its mixed-Rees defect support must be realized by ordinary ambient blowups in actual regular centres which are simultaneously active-permissible, passive/Tor-safe, and logarithmically transverse. The maximum-likelihood closure uses induction on the strictly smaller carrier support with the complete owner portfolio.

---

## 1. Centre-exact terminal transform

A finite composition of blowups in finitely presented centres is a blowup in a finitely presented composite centre. Strict transforms compose for this centre. Therefore, if `E` is the total exceptional divisor of the centre-exact composite blowup and `F^iter` is the final iterated strict transform, then

```text
F^iter = p^*F / H^0_E(p^*F),
H^0_E(F^iter) = 0.
```

In the coherent Noetherian setting one finite exponent `N` computes the torsion submodule, hence

```text
F^iter = H^0((Lη_{I_E})^N Lp^*F).
```

This closes the terminal actual-to-saturated comparison inside the finite ordinary-blowup category. It does not license forgetting the composite centre.

---

## 2. Regular-flag chart algebra

Etale locally write

```text
I_C=(x_1,...,x_r),
I_D=(x_1,...,x_r,y_1,...,y_s).
```

Only a `y`-pivot chart meets `C'`. On `q=y_1`,

```text
B=R[I_D/q],
I_C B = q I_{C'}.
```

For an owner `M` set `N=M⊗_R B`, `T=H^0_(q)(N)`, `M'=N/T` and

```text
F_n=image(I_C^n M⊗B -> N),
C_n=F_n/F_(n+1).
```

There are canonical maps

```text
(I_C^n M/I_C^(n+1)M)⊗B
   --alpha_n--> C_n
   --beta_n--> q^n(I_C'^n M'/I_C'^(n+1)M').
```

The three defects are

```text
T_n=ker(alpha_n),
V_n=ker(beta_n),
S_n=coker(beta_n).
```

`T_n` is the Tor/base-change defect; `V_n` is the Valabrega intersection defect; `S_n` is the saturation-generation defect. All vanish off the exceptional divisor.

---

## 3. Finite mixed-Rees compression

The direct sum over all degrees is a finite module over the mixed-Rees algebra

```text
⊕_{a,b>=0} I_C^a I_D^b U^a V^b.
```

No fixed jet cutoff is used. Homogenization by `z` gives a proper coherent all-degree packet on

```text
P_C(O_C ⊕ I_C/I_C²).
```

The open `D_+(z)` is the full affine normal cone and recovers every low degree. Flatness of the homogenized packet is equivalent to flatness of every original normal piece.

---

## 4. Flat-kill closure

Let `U` be the good open on which the comparison is already an isomorphism. Functorial/admissible flatification gives a `U`-admissible blowup on which the strict transform of the comparison packet is flat. Since `U` meets every irreducible component, the transformed packet vanishes at all minimal primes. If `A` is reduced Noetherian and `Q` is `A`-flat, then

```text
Q_p=0 for all p in Min(A)  =>  Q=0,
```

because `A` injects into the finite product of its minimal-prime localizations and flat tensor preserves this injection. Hence the entire comparison packet vanishes simultaneously in every degree and for every owner.

---

## 4A. Universal exactification

Flatifying only the direct sum `T_n ⊕ V_n ⊕ S_n` is insufficient: after a nonflat base change, kernels and images need not be the pullbacks of the old kernels and images. X042 therefore enrolls, in every degree and for every owner,

```text
A_n, C_n, B_n,
ker(alpha_n), im(alpha_n),
ker(beta_n), im(beta_n), coker(beta_n),
```

as well as the multiplication-image sequences defining the graded structures. If all these modules are flat, the short exact sequences defining `alpha_n` and `beta_n` remain exact after arbitrary base change, because the relevant `Tor_1` terms vanish. Thus formation of all three defects commutes with every subsequent centre-exact pullback.

This exactification removes a hidden circularity from the flat-kill argument. What remains open is geometric rather than homological: the regular ambient trace word must pull this universal mixed-Rees diagram to the actual successor normal comparison on every chart and overlap.

---

## 5. Terminal source realization

A finite family of `U`-admissible source blowups admits one `U`-admissible common refinement. If the terminal source owner is flat, its strict transform under any further blowup is its pullback. Composition of strict transforms gives a canonical identification of every source terminal packet on the common model. Thus the former source-word realization burden reduces to:

- standard centre-exact strict-transform composition and flat persistence;
- project-specific ambient trace realization and source/boundary descent.

---

## 6. Candidate-graph delta

### Closed or reduced to standard scheme theory

- X042-G1 centre-exact finite blowup-word compression;
- X042-G2 terminal full exceptional saturation and no terminal recharge;
- X042-G3 finite `H^0(Lη)` realization;
- X042-G4 chartwise alpha/beta comparison construction;
- X042-G5 exact typing of Tor, Valabrega, and saturation defects;
- X042-G6 finite mixed-Rees all-degree packet;
- X042-G7 homogenized affine-normal-cone recovery;
- X042-G8 reduced-base flat-kill;
- X042-G9 exactified carrier-side comparison vanishing after admissible preparation on a fixed centre-exact chart;
- X042-G10 terminal flat-source common-refinement realization.

### Still load bearing

- X042-G11 functorial selection of source flatifiers in the full intrinsic groupoid;
- X042-G12 regular ambient realization of carrier flatifier ideals;
- X042-G13 joint active/passive/logarithmic legality of every preparatory centre;
- X042-G14 all-chart owner/source/boundary/contact transport;
- X042-G15 support-thickness strict descent for every bad intersection;
- X042-G16 strict global causal rank;
- X042-G17 finite globalization and functorial resolution.

### Highest-information next cut

```text
AMBIENT REGULAR TRACE REALIZATION
  -> ALL-CHART STATE REENTRY
  -> STRICT GLOBAL TERMINATION.
```

---

## 7. Truth boundary

The X042 carrier-side comparison architecture is substantially sharper than X041: exceptional recharge is removed as an internal branch, the complete comparison is one finite coherent mixed-Rees exactification portfolio, and on a fixed centre-exact chart its vanishing after flatification is reduced to universal exactness plus the standard flat-kill argument. The identification of this prepared portfolio with the actual successor ambient comparison, the regular ambient realization, and the final global termination theorem are not established in the research baseline. General arbitrary-dimensional positive-characteristic resolution remains open.
