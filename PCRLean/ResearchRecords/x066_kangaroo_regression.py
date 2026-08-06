#!/usr/bin/env python3
"""Exact GF(2) regression calculation used in X066, Section 8."""
from __future__ import annotations

import sympy as sp

x, y, z = sp.symbols("x y z")


def mod2(expr: sp.Expr) -> sp.Expr:
    return sp.Poly(sp.expand(expr), x, y, z, modulus=2).as_expr()


def main() -> None:
    f0 = x**2 + y**7 + y*z**4
    f2 = x**2 + y**3*z**3*(y**2 + z**2)
    f3_raw = x**2 + z**6*(y**5 + y**4 + y**3 + y**2)
    f3 = mod2(f3_raw.subs(x, x + y*z**3))
    expected = x**2 + z**6*(y**5 + y**4 + y**3)
    assert mod2(f3 - expected) == 0

    g2 = y**2 + z**2
    g3 = y**5 + y**4 + y**3
    dy_g2 = mod2(sp.diff(g2, y))
    dz_g2 = mod2(sp.diff(g2, z))
    dy_g3 = mod2(sp.diff(g3, y))
    dz_g3 = mod2(sp.diff(g3, z))

    assert dy_g2 == 0 and dz_g2 == 0
    assert mod2(dy_g3 - (y**4 + y**2)) == 0 and dz_g3 == 0

    print("f0      =", f0)
    print("f2      =", f2)
    print("f3_raw  =", f3_raw)
    print("f3_clean=", f3)
    print("dg2     =", (dy_g2, dz_g2))
    print("dg3     =", (dy_g3, dz_g3))
    print("packet  : shade 2 -> 3; Cartier height 1 -> 0; differential-Fitting profile (2,2) -> (1,1)")


if __name__ == "__main__":
    main()
