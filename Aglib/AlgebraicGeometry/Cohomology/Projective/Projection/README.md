# Relative projective-space projections

`Coherence` proves `Scheme.Cohomology.projectiveProjection_higherDirectImage_coherent`.
The input is an original Cartesian square over the actual structural map
`ProjectiveSpace.toSpec R ι`, together with a coordinate equivalence
`ι ≃ Fin (n + 1)`. If the new base is locally Noetherian, every actual
natural-degree higher direct image of an affine-locally finite-type
quasicoherent coefficient is affine-locally finite type. This is the
coherent condition on these locally Noetherian schemes.

The original ring `R` is arbitrary, the base need not be quasi-compact, and
the coefficient need not be relatively flat. Dimension zero is included.
The result concerns the original `(Scheme.Modules.pushforward p).rightDerived q`.
There is no projective-coherence or proper-finiteness theorem-family input.

On each actual affine chart of the base, `ProjectiveSpace.BaseChange.Affine`
identifies the original Cartesian square with polynomial projective space
over that chart ring, retaining its original structural map. The proved
embedded-projective finiteness theorem gives finite unchanged `Sheaf.H`.
The sole original affine higher-image section comparison and open-restriction
comparison then transport that finite generation to the actual higher image.

`Vanishing` proves `projectiveProjection_higherDirectImage_isZero`: the same
original higher image is zero whenever `n < q`, over an arbitrary base and
for every quasicoherent coefficient. This does not require Noetherianity,
finite generation or relative flatness. Its affine-base helper retains the
unchanged `Sheaf.H`; the original `n + 1` coordinate opens give the sharp
bound. Native affine higher-image sections and the actual tilde--Gamma
counit then detect the zero sheaf on each base chart.

`Amplitude` proves the corresponding bound for the installed actual
`Scheme.Modules.derivedPushforwardPlus`. A quasicoherent module placed in
integer degree `i` has derived image bounded above by `i + n`. More generally,
an object whose original homology is bounded in `[l,b]` and quasicoherent in
that interval has derived image bounded in `[l,b+n]`. There is no condition
on a chosen complex's terms. The proof uses the native single-functor shift
comparison, the sole finite Postnikov induction and the generic lower-bound
theorem for the installed right-derived functor. The base remains arbitrary.

`Derived` proves preservation of the sole shared
`Scheme.Modules.coherentHomologyObjects` property for every cohomologically
bounded object. Its single-coefficient result covers all integer placements;
the bounded result uses exactly the shared native Postnikov induction.
`projectiveProjection_derived_bounded_coherent` gives both coherence and the
interval `[l,b+n]` for the original installed derived direct image. The
locally Noetherian source guard forms that shared input property and follows
from finite type of the projective projection over the locally Noetherian
base. It is not a relative-flatness hypothesis or a condition on complex terms.

The [finite native product](../Products/README.md) consumer now iterates this
same theorem with the original derived composition and the sum of the
displayed dimensions. The [proper Chow](../../Proper/Chow/README.md) and
[support-induction](../../Proper/SupportInduction/README.md) consumers use
these same bounded coherent images in the actual modification cone.
