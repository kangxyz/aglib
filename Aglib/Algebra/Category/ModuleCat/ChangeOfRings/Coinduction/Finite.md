# Finite generation of the original higher-coinduction homology

Let `q : R →+* S` be a map of commutative rings in universe `u`, let `R`
be Noetherian, and let `N : ModuleCat.{u} R`. Assume that `N` and the
actual restricted regular module `(restrictScalars q).obj (of S S)` are
finite over `R`.

`ModuleCat.coinducedExtSourceModule_finite` proves, in every natural
degree, finite generation over `S` of the original ambient Ext carrier
equipped with the explicit action from `SourceAction`. Its selected Ext
size is arbitrary. The proof has three steps:

1. Native `ModuleCat.finite_ext` gives finite generation for standard-size
   Ext. `Ext.chgUnivLinearEquiv` transfers it to the selected size through
   the unchanged native universe comparison.
2. The identity on that original Ext carrier is `q`-semilinear because
   `coinducedExtSourceModule_map_smul` proves that `q r` acts as the
   original ambient scalar `r`.
3. `Module.Finite.of_surjective` transfers the finite generating set along
   this identity. This lemma does not require surjectivity of `q`.

`ModuleCat.derivedCoextendScalarsPlusHomology_finite` then proves that the
same degree of homology of the installed D+ right-derived coinduction at
the original degree-zero single is finite over `S`. It uses the unchanged
`derivedCoextendScalarsPlusHomologyExtSourceLinearEquiv`. Both supplied
derived-category sizes remain independent; no new Ext size is added to
the homology theorem's interface.

Neither statement requires locality, a surjective ring map, flatness,
projectivity, concentration, an action of `S` on the coefficient, or a
canonical trivialization. The regular-quotient canonical modules in
[`Gorenstein/NormalQuotient`](../../../../../RingTheory/Gorenstein/NormalQuotient.md)
are a current consumer: surjectivity supplies the finite restricted
source, and a genuine ambient coefficient-line frame supplies a finite
coefficient.

This is the finite-generation condition in the standard dualizing-complex
definition ([Stacks, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)).
Together with the separately proved injective-dimension bound it still
does **not** prove the original homothety quasi-isomorphism, dualizing
uniqueness, or intrinsic Gorensteinness implying canonical triviality.
