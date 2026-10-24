# The actual two-layer dual obstruction

`TwoLayerDual` works with a commutative ring map `sigma : R → A`, the
supplied injective resolution of the original regular R-module, and its
literal coinduced coefficient complex J. The original restriction of A
is projective over R. For a regular local R of dimension two, the actual
restriction of H has finite length.

The input triangle is literally

```
single 0 A --eta--> C --kappa--> single 1 H --delta--> (single 0 A)[1].
```

Its distinguishedness is a hypothesis about these actual arrows. No
splitting, perfect-model, evaluation, trace-compatibility or triangulated
structure on the constructed dual is supplied as a premise. No normality,
injectivity or locality condition on A is needed. Projectivity of the
restricted A-module suffices for this supplier; surface applications also
have finiteness.

The shared
[Cohomology/Derived.lean](../Cohomology/Derived.lean) comparison supplies
native A-linear dual homology and original derived Hom, naturally for
every actual derived morphism. `singleOneHomEquiv` uses the native
single/shift comparison, shift autoequivalence and shift composition;
it moves source degree one to target degree n+1 without assigning a
new shift structure to the dual.

`unitNormalization` uses the actual coinduced augmentation and evaluation
at one. The row maps are:

- `unitMap`: original H0 of the dual of eta, followed by that normalization;
- `boundaryMap`: native unsigned `ShiftedHom.comp delta`, transported
  through the fixed shared comparisons;
- `projectionMap`: original H1 of the dual of kappa.

Their comparison theorems retain the actual unit, connecting arrow and H1
map. `obstruction_exact` gives the exact A-linear sequence

```
0 → H0(D_J C) → Hom_R(A,R) → H1(D_J(single 1 H)) → H1(D_J C) → 0.
```

The existing R-Ext-two theorem computes only scalar restrictions of the
intrinsic A-modules. Its finite-length conclusion and the actual last-row
surjection prove `homologyOne_finiteLength` for the original A-action.
This R-linear comparison is never asserted to be an A-linear map.

`homology_isZero`, `isGE_zero` and `isLE_one` give the actual dual amplitude
[0,1] from the two outer Yoneda groups. These bounds and finite-length H1
supply the subsequent nonzero-residue obstruction argument. They do not
assert that H1 vanishes or that the algebraic dual-unit map is the
geometric trace. The file does not depend on the finite-projective
model construction in `TwoLayer.lean`.

The canonical `unitPostnikov_isGE_zero`, `unitPostnikov_isLE_one` and
`unitPostnikov_homologyOne_finiteLength` wrappers take the actual Plus
object X with its [0,1] bounds, the specified unit eta with its native H0
isomorphism, and finite R-length of its original H1. They use
`unitPostnikovTriangle`, the image of the original native Plus triangle.
The single endpoints agree definitionally because `singleFunctorιIso`
is the native reflexive comparison. No extra triangle, connecting map
or model premise is supplied by the caller.

`unitPostnikovTriangle_mor₁`, `_mor₂` and `_mor₃` display the original
arrows; the last formula retains the inclusion's native shift comparison.
`unitPostnikov_obstruction_exact` exposes the same normalized unit and
unsigned boundary row for the later geometric trace comparison.

The native endpoint abbreviations `regularSource`, `firstLayer` and
`resolutionCoefficient` are the literal original single objects and
coinduced resolution complex. They replace dependent local notation; no
object or arrow is selected anew. The augmentation proof explicitly uses
the native inverse single comparison's quasi-isomorphism and the original
coinduced augmentation map. `hd`, `hH`, the actual distinguished triangle
and the original unit are retained in the theorem signatures where their
proofs use them. These are the intended dimension, finite-length and
original-triangle conditions already stated above.

The subsingleton facts use the literal bridge and triangle-object carriers.
Negative coefficient degrees use the fully qualified cochain bound, and the
natural-degree exclusion follows from the supplied integer-degree exclusion.
The projectivity, dimension, finite-length and triangle conditions remain
explicit on the obstruction row and amplitude results.
