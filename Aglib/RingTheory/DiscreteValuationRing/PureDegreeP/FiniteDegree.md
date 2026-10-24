# Finite DVR degree and original pth powers

[FiniteDegree.lean](FiniteDegree.lean) proves finite DVR degree formulas and
pth-power descent through the original fraction fields.

For a finite torsion-free extension of actual DVRs A → B, it derives

```text
ramificationIdx(maximalIdeal B, A) * [κ(B) : κ(A)] = finrank A B.
```

Finite torsion-free modules over a DVR are free, hence flat. The native
finite-flat ramification formula applies. There is only one prime above the
maximal ideal of A: integrality makes every such prime maximal, and B is local.
Thus its native sum has one term. This uses neither separability nor a
perfect field, and it does not assume a defectless equation.

If the original image of a source uniformizer is `u * τ^e`, the native
ramification index equals that literal e. The proof compares the original
extended maximal ideal with `(maximalIdeal B)^e` and uses strictness of the
native DVR ideal order. `IsFractionRing.finrank_eq` then identifies the module
rank with the actual fraction-field degree. In prime degree p, the two cases
are `(e,f)=(p,1)` and `(e,f)=(1,p)`.

For a finite purely inseparable extension L/K of degree p in characteristic p,
the minimal-polynomial degree bound gives `p^(elemExponent K x) ≤ p`, hence
every original `x^p` lies in the image of K. If b belongs to the finite
A-algebra B, its pth power is integral over A. Normality of A places the
corresponding K-element in A; injection into the actual fraction field gives
`algebraMap A B a = b^p` on B itself.

The field statements explicitly use `CharP K p` and `Fact p.Prime`. In the
intended application `CharP A p` transports to K by the fraction localization.
The first degree theorem is characteristic-free and does not require a
purely inseparable extension. Its current consumer is the companion
monogenicity module.
