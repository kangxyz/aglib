# Flat integral sources over a Dedekind base

Import `Aglib.AlgebraicGeometry.Morphisms.Flat.DedekindBase`.

`Scheme.Hom.flat_of_isIntegral_of_isDominant` treats an actual morphism
`p : Z ⟶ Spec A`, where `A` is a Dedekind domain, `Z` is integral, and `p` is
quasi-compact and dominant. It proves `Flat p` for that same morphism. No
Noetherianity, regularity, dimension or finite-type condition on `Z` is added.

Dominance gives the original scheme-theoretic dominance over the reduced
base. If an original stalk map kills a section, the original integral-source
germ map detects its vanishing. The resulting stalk-map injectivity makes
each original source stalk torsion-free over the corresponding actual
localization of `A`. Native Dedekind-domain torsion-free flatness then gives
the original morphism flat by the stalk criterion.

This is the existing flatness argument used by the actual trait graph,
extracted to its lower native owner so other integral proper modifications
can use it without importing a surface construction. It retains the displayed
quasi-compactness hypothesis. It does not assert regularity or that an
arbitrary morphism to a Dedekind base is flat.
