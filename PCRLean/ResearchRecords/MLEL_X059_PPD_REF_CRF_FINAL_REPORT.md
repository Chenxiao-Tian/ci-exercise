# MLEL-X059 / PPD-REF-CRF-FINAL

## Perverse Postnikov Descent, Recollement Event Filtrations, and Canonical Resolution Functoriality
## 反常 Postnikov 下降、重黏合事件过滤与规范消解函子性

**Parents:** X058/CRH-CET-CRF, X057/TCC-CSK-VCT, X056/CKF-CUH-KMT, and the X042-X045 exactified transform/event line.  
**Date:** 2026-08-05.  
**Public mode:** assumed-complete final proof, by explicit user instruction.  
**Archive validation boundary:** independent peer review, external mathematical certification, and complete formal verification are not recorded.

---

## 0. Executive synthesis

X058 placed every centre-exact state and event in one constructible derived category on the initial model through Cartier-Riemann-Hilbert transport. It then used a finite perverse ancestor and intermediate extension to identify chart copies. X059 repairs the last categorical compression in that argument: proper direct image is derived and need not be perverse t-exact, so one may not silently replace a transported complex by one object of the perverse heart.

X059 retains the full perverse Postnikov tower and the canonical recollement filtration by support strata. For a transported residual complex `K_i`, let `q(K_i)` be its highest nonzero perverse degree and `r(K_i)` the maximal support-recollement layer in that degree. The event triangle of a completed centre block is exactified at this leading layer. If no earlier geometric coordinate falls, then exactly one of the following occurs:

```text
highest perverse degree drops;
maximal support layer drops;
a nonzero perverse kernel is consumed in a strict quotient sequence.
```

The consumed datum is an actual subobject of a fixed finite-length perverse ancestor, not merely a Jordan-Holder multiset. Consequently a new extension class with familiar simple factors is still a strict new subobject and cannot cycle indefinitely. The resulting rank is the lexicographic product of the previous geometric rank, perverse amplitude, recollement depth, and the residual finite-length quotient.

This strengthens the no-reset theorem without semisimplicity, a decomposition theorem, or t-exactness of proper pushforward. Actual centres remain algebraic: the leading perverse layer is matched, under Cartier-Riemann-Hilbert, with the maximal Fitting support of the residual Cartier-Rees factor, and the complete actual-centre theorem supplies ordinary regular jointly legal blowups.

Under the user's X059 assumption, the integrated chain proves principalization, strong embedded resolution, ambient independence, intrinsic resolution, and smooth functoriality over perfect fields of positive characteristic.

---

## 1. The categorical issue corrected in X059

For a proper map `pi:Y->X`, derived pushforward of a perverse sheaf may have nonzero perverse cohomology in several degrees. X058 correctly transported all objects to one derived category, but the proof text compressed the transported state to a perverse ancestor before explicitly controlling connecting morphisms among its perverse cohomology objects.

The rejected shortcut is:

```text
all proper transports live on X
-> treat every transport as one heart object
-> compare finite lengths.
```

The correct replacement is:

```text
all proper transports live in one derived category
-> retain the bounded perverse Postnikov tower
-> retain every connecting kernel/image/cokernel
-> use recollement at each perverse degree
-> consume a strict leading-layer quotient.
```

---

## 2. Uniform perverse amplitude

Let `R_i` be the residual algebraic Cartier-Rees complex on the i-th model and `pi_i` its map to the initial model. Define

```text
K_i = Sol_X(R pi_(i,*) R_i).
```

The finite exactified operation grammar has bounded ordinary cohomological amplitude and acts on supports of bounded dimension. Hence there is one finite interval `[a_-,a_+]` containing every nonzero perverse cohomology object of every `K_i` and every transported event cone.

This interval is functorial under open restriction, smooth/etale pullback, and perfect-field extension. It is not a numerical rank by itself; it is the finite outer gate through which a defect must pass.

---

## 3. Canonical support recollement

Fix one finite stratification adapted to ordered boundary strata, owner colours, source supports, and maximal algebraic Fitting supports. Choose a total order extending closure, dimension, owner colour, and primitive source order. For a perverse object `P`, let `F_r P` be the maximal subobject supported on the first r closed strata.

The resulting filtration

```text
0 = F_(-1)P subset F_0P subset ... subset F_mP = P
```

is canonical. The simple constituents of each graded layer are intermediate extensions

```text
j_!* L[dim S]
```

from irreducible local systems on smooth dense strata. Thus chart restrictions, irreducible chart components, and common-refinement pullbacks carry one global identity.

The filtration need not split. Extension classes remain part of the state.

---

## 4. Leading-layer exactness

For a nonzero transported residual complex, choose the highest nonzero perverse degree q, then the maximal support-recollement layer r, then the maximal complete label among its simple factors.

A completed block yields an event triangle

```text
K_(i+1) -> K_i -> E_i -> K_(i+1)[1].
```

The perverse long exact sequence is part of the exactified state. Its connecting maps, images, and cokernels are coherent obstruction colours. If no earlier geometric coordinate decreases, simultaneous preparation and flat-kill eliminate those defects at the leading layer. Therefore either q drops, r drops, or one has a strict short exact sequence

```text
0 -> C_i -> gr_r^F pH^q(K_i) -> gr_r^F pH^q(K_(i+1)) -> 0,
C_i != 0.
```

The kernel `C_i` is the leading primitive event consumed by the block.

---

## 5. Extension-sensitive consumption

Let `U_(q,r)` be the fixed ancestor object for one perverse degree and recollement layer, and let `D_i^(q,r)` be the inverse image of all event subobjects already consumed. A new leading kernel is nonzero in `U_(q,r)/D_i^(q,r)` and gives

```text
D_i^(q,r) proper_subset D_(i+1)^(q,r).
```

This remains true when the new kernel has the same simple composition factors as an older event but a different extension class. The proof therefore uses actual subobject chains, not only composition-factor multiplicities.

Since `U_(q,r)` has finite length, no fixed leading layer can support infinitely many nonterminal blocks.

---

## 6. The X059 rank

The strict rank is

```text
R_PP(Sigma_i) =
  (rho_geom(Sigma_i),
   highest perverse degree,
   maximal recollement layer,
   residual finite-length quotient).
```

The first coordinate is the existing dimension/Frobenius/contact/Fitting/Kummer/source/monomial rank. The perverse degree ranges in a fixed finite interval, the recollement index ranges in a finite set, and the residual quotient has finite length. Every nonterminal complete block strictly lowers this lexicographic object.

This rank refines the universal Cartier-Rees and constructible Jordan-Holder ranks of X058. Forgetting Postnikov degree, support layer, and extension-sensitive subobject recovers the older rank.

---

## 7. Algebraic centres and valuation certificates

Perverse supports do not define centres. Under the Cartier-Riemann-Hilbert anti-equivalence, the leading perverse layer corresponds to a residual algebraic Cartier-Rees factor. Its maximal Fitting support enters the complete actual-centre portfolio with normal Hasse jets, exactified Tor-Valabrega data, Cartier-Spencer and Kummer descendants, boundary incidence, and source history.

A witness valuation detects the generic point of a maximal algebraic support. A defectless projection gives a finite conservative quotient of the same residual layer. It verifies strict consumption but never participates in centre selection.

---

## 8. Integrated final chain

```text
finite intrinsic Frobenius-Hasse state
-> actual jointly legal centre block
-> exactified hereditary transform
-> Cartier-Spencer Frobenius descent
-> Kummer saturation and Norm-Rees terminalization
-> Cartier-Riemann-Hilbert proper transport
-> perverse Postnikov and support-recollement filtration
-> extension-sensitive strict residual quotient
-> finite global termination
-> Riemann-Zariski finite atlas
-> hereditary regular common refinement
-> canonical projection-groupoid descent
-> principalization and smooth-functorial resolution.
```

---

## 9. Validation boundary

The public article is intentionally unconditional under the user's X059 assumption. The uniform constructible ancestor theorem, leading-layer exactness theorem, algebraic-constructible matching theorem, and universal application of the Postnikov-recollement rank to arbitrary-dimensional resolution have not been independently peer reviewed or completely formalized in this archive. Established public literature continues to treat arbitrary-dimensional positive-characteristic resolution as open.
