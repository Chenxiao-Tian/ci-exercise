# MLEL-X038 Supplement — Exceptional Filter-Regularity

With

```text
T=H^0_(u)(N), A=gr_L(N), H=gr_L^ind(T), U=H^0_(u)(A), E=U/H,
```

the X038 identity gives

```text
E = H^0_(u)(gr_L(N/T)).
```

Consequently `E=0` exactly when the exceptional equation `u` acts injectively on the associated graded of the purified module. The interchange packet is therefore a filter-regularity/saturation defect rather than an arbitrary transform discrepancy.

The identity also follows from local cohomology. Since `H` is killed by a power of `u`, the exact sequence `0 -> H -> A -> A/H -> 0` yields

```text
0 -> H -> H^0_(u)(A) -> H^0_(u)(A/H) -> 0,
```

so `H^0_(u)(A/H)=U/H`. This is the natural route to sheafification along an effective Cartier exceptional divisor.

For an SNC exceptional boundary the finite packet is locally killed by one exceptional monomial. Its exponent vector is a finite source-labelled debt/contact coordinate. The all-chart comparison, divisorial elimination and no-recharge theorem remain open; `FORMAL_GLOBAL_STATUS=OPEN_GAP`.
