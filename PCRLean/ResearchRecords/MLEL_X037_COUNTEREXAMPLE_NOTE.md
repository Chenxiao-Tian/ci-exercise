# X037 counterexample note: strict target is not the actual ambient packet

Let `X=Spec k[u,x]`, let `C=V(x)`, and let `D=V(u,x)`.  For `m>=2`, set
`Y_m=V(x-u^m)`.

On `C`, the projective-normal packet of `O_{Y_m}` is `O_C/(u^m)`.  Since `D`
is Cartier on `C`, `Bl_D(C)=C`, and the ordinary strict transform of this packet
is zero.

On the ambient `u`-chart of `Bl_D(X)`, write `x=ut`.  Then

```text
x-u^m = u(t-u^(m-1)),
```

so the strict transform of `Y_m` is `t-u^(m-1)=0`.  Along `C'=V(t)`, its actual
projective-normal packet is `O_C/(u^(m-1))`, not zero.

Therefore an ambient-lift theorem may not identify the actual transformed
projective-normal packet with the carrier strict transform.  The correct
comparison can hold only after exceptional saturation; the finite discrepancy
is the exceptional saturation debt.

This note is a mathematical countermodel record, not a Lean theorem and not a
claim that the proposed bi-Rees comparison has been proved.
