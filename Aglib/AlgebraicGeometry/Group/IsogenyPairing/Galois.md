# The actual Galois-equivariant kernel pairing

`Galois.lean` specializes the positive frame-transport construction to the
original geometric points of a finite etale isogeny. Its public declarations
live in `AlgebraicGeometry.Scheme.Group.IsogenyPairing.Galois`.

## Inputs and output

Let `F` be a field and let `f : E ⟶ D` be finite, etale and surjective. Both
original group schemes satisfy native `Curve.Properties`, and both native
coherent genera equal one. The input `HasGeometricDegree f.hom.hom n` refers to
every algebraically closed geometric fibre of the actual map. A given
`d : D ⟶ E` satisfies the source multiplication triangle
`f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n`.

`GeometricKernelPoints f` is the type of actual morphisms from the chosen
algebraic-closure point to `Kernel.group f`. `geometricPairing` has type

```lean
Additive (GeometricKernelPoints d) →+
  (Additive (GeometricKernelPoints f) →+
    Field.absoluteGaloisGroup.RootsOfUnity.Mu F n)
```

`geometricPairing_bijective` additionally assumes `IsUnit (n : F)`.
`geometricPairing_galois` proves simultaneous equivariance for literal
`FieldGalois.pointEnd` precomposition and the native absolute-Galois action on
actual roots of unity. `perfectPairing` packages this constructed map,
bijectivity and equivariance in `PerfectPairing f d n`.

The statements work in arbitrary characteristic with the stated invertibility
condition for perfectness. No reverse-degree premise, Picard representing
witness, chosen kernel coordinates or chosen cyclotomic character occurs in
the construction.

## Actual comparison maps

`pointEquiv` is the native pullback adjunction on geometric points.
`kernelEquiv` uses that adjunction and the actual kernel universal properties
to compare the original geometric kernel with the kernel after closure
extension. It preserves the original kernel inclusion and group law.
`fieldProperties`, `fieldGenus`, `fieldDegree` and `fieldTriangle` transport
the given geometric hypotheses through actual base change.

For a field automorphism `σ`, `familyIso` is the literal scheme map
`id × pointEnd(σ)` on the base-changed curve. `pointSquare` compares it with
point precomposition. `translationSquare` follows from these equations and
reduced finite-type curve extensionality. The semilinear point-ideal and frame
transport theorems then prove the roots-of-unity equation.

`geometricPairing_fundamentalGroup` additionally assumes characteristic zero
and states the same equation for the actual field fundamental group through
the proved continuous equivalence with the absolute Galois group. The original
point maps and scalar action remain explicit in that equation.

## Boundary

This module proves the perfect arithmetic pairing for the stated native
curve and coherent-genus hypotheses. Identifying another presentation of
elliptic geometry with those hypotheses is a separate application step.
Weil alternation is not supplied by this module.
