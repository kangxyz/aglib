# Concentrated derived coinduction and Ext

`derivedCoextendScalarsPlus_isGE_of_ext` and `_isLE_of_ext` convert native
ambient Ext vanishing to the actual installed derived coinduction bounds.
Negative degrees use its native left t-exactness.

`concentratedCoextendScalarsExtAddEquiv` identifies
`Ext_S^k(N, H^n(R coind_q M))` with `Ext_R^(k+n)(Res_q N, M)` when the
original `Ext_R^j(Res_q S,M)` vanishes outside `n`. This holds for every
source module `N`, not just finite modules. It uses the original derived
adjunction, the native homology-normalized single isomorphism and installed
single/shift comparisons. There is no assumption that `S` is projective
or flat over `R`.

The two Ext sizes and both derived-category sizes are independent. The rings are commutative. Ring
and module carrier universes are common, as in the native coinduction Ext
comparison. The coefficient is the actual target-ring homology module;
its action is not replaced by an ambient linear model.
