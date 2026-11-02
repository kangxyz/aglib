# Original normalization chart sections

Fix an integral scheme `X` and the specified field `F` with its original
`X.functionField`-algebra. Let `gamma : Spec F -> X` be the existing generic
map, `N` its literal relative normalization, `pi : N -> X`, and
`eta : Spec F -> N` the original factorization.

For each nonempty affine open `U` of `X`, `normalizationSectionsEquiv`
identifies the ACTUAL section ring `Gamma(N, pi^-1 U)` with
`integralClosure Gamma(X,U) F`. The original source algebra is `pi.app U`;
the ambient action is `chartAmbientAlgebra`, the actual generic germ followed
by the given map to `F`. This named action and its scalar-tower law are used
locally, not installed as competing global instances.

The construction composes the native `normalizationObjIso` ring equivalence
with `mapIntegralClosure` of the existing `chartFieldEquiv`. Its coefficient
law follows from the original `fromNormalization_app` equation. No separate
intermediate algebra-equivalence implementation is added.

`normalizationSectionsEquiv_val_comp` retains the whole original ambient
RingHom: closure value after the section equivalence is the original
`eta.appLE` followed by the original `chartFieldIso`. Its proof consumes the
native `normalizationObjIso_hom_val` once. The existing pointwise
`normalizationSectionsEquiv_val` is its evaluation at the original section,
not a second geometric value calculation. The latter field-chart comparison
preserves every nonempty-open restriction.
Consequently, for any nested nonempty affine opens `V <= U`, the original
normalization section restriction is, in these exact coordinates, the native
same-ambient `integralClosure.scalarExtensionHom`.

The principal-open corollary identifies the actual normalization section
map as localization, using its original affine preimage and the existing
native `IsAffineOpen.isLocalization_basicOpen`. Combined with the preceding
whole restriction square, it is the same closure localization, not a new
construction. The localization assertion itself allows empty principal
opens and makes no domain assertion about their zero section ring; the
field-valued equivalences still require nonempty opens.

No finite field extension, Nagata, normality of `X`, Noetherianity, surface,
characteristic, or differential hypotheses are used. Original finite-cover
trace is a later consumer. Its actual `Cover.normalization` is retained by
the existing exact `genericMap_eq`; identification with a separately supplied
field must retain its canonical fraction-field map triangle.
