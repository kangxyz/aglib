# Degree-zero flat base-change unit square

The public declaration
`AlgebraicGeometry.Scheme.Modules.higherDirectImageFlatBaseChangeMap_zero_unit`
compares the installed higher-direct-image base-change map in degree zero with
the original cartesian base-change map. Its inputs are four actual scheme
arrows forming the supplied pullback square, flatness of the base arrow `j`,
and an arbitrary module sheaf `M` on its upper-right scheme. It introduces no
properness, finiteness, quasicoherence, or supplied comparison premise.

Writing `F = pushforward f`, `J = pullback j`, `A = pullback a`, and
`B = pushforward b`, the statement retains the literal equation

```text
J.map (F.toRightDerivedZero.app M) ≫ higherBaseChange₀.app M
  = cartesianBaseChange.app M ≫ B.toRightDerivedZero.app (A.obj M).
```

The proof first identifies the original map to the zeroth right-derived
functor with homology of the installed bounded-below derived unit. This uses
the actual chosen injective resolution, its augmentation extended to integer
cochains, the original zero-cycle arrow, and the native localization/homology
factorization. It then applies the existing derived flat base-change unit
equation to the degree-zero single complex. The original single-complex maps
for compositions and natural transformations retain the ordinary cartesian
base-change arrow. Finally, the native exact-single/homology coherence for
the flat pullback transports that equation to the displayed square.

Auxiliary constructions stay in this consumer, and its derived-category
instance is local. This result concerns
the unit square only; it supplies neither a new base-change isomorphism
criterion nor a proper-object algebraization theorem. Native compilation
status is recorded in the source-bound author handback, independently of this
mathematical description.
