# X056 Supplement: Logarithmic Cartier Kernel and Unit Firewall

For a smooth SNC pair `(R,E)` over a perfect field with characteristic monoid `P`, define

```text
dlog : R^* x P^gp -> Omega^1_R(log E),
(u,b) |-> dlog(u)+sum b_i dlog(x_i).
```

The kernel is the image of `p`: a logarithmic monomial has zero logarithmic differential exactly when its unit is a pth power and its exponent vector is divisible by p. The proof is etale local in standard coordinates.

This corrects the X055 shorthand. `du=0` implies `u=v^p`, but `dv` need not vanish. The correct operation is one Cartier peeling step, followed by a new logarithmic Jacobian test. The total residual Cartier height is finite and decreases.
