# X056 Last-Chance Proof Audit

## Interfaces re-audited

- Root presentation dependence: removed by the intrinsic height-one foliation and canonical Frobenius filtration.
- Centre descent through radicial quotients: typed by full relative Hasse stability and proved degreewise on Rees algebras.
- Terminal unit coefficients: handled by `ker(d)=R^p`, not by informal unit absorption.
- Terminal toric source: regularized base-first by Ferrand norm ideals and ordinary regular-centre principalization; normalized blowup is not the output.
- Projection choice: excluded from the algorithm and retained only as a termination certificate.
- Infinite sequence extraction: uses nested closed nonterminal cylinders in the quasi-compact Riemann-Zariski space.
- Functoriality: follows from one-step intrinsic base-change compatibility after finite termination.

## Final logical chain

```text
foliation/Hasse state
-> actual legal centre
-> strict all-chart descent
-> logarithmic straightening or Norm-Rees terminalization
-> full Frobenius-envelope uniformization
-> defectless projection certificate
-> valuation-certificate termination
-> global embedded resolution
-> principalization and functorial intrinsic resolution.
```

## Validation boundary

The public article is unconditional under the X056 assumption. Independent peer review and complete formal verification are not recorded in the archive.
