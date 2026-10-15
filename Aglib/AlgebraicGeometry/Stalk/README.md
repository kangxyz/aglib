# Polynomial and generic-fibre stalks

[Polynomial](Polynomial.lean), imported as `Aglib.AlgebraicGeometry.Stalk.Polynomial`, gives native `Scheme.polynomial_spec_stalk_isRegularLocalRing`, the all-prime dimension bound and the maximal-prime dimension equality for finitely many polynomial variables over an arbitrary field. The maximal residue extension need not be separable.

[GenericFiber](GenericFiber.lean) uses `AlgebraicGeometry.Scheme.LocalRing.GenericFiber`. For `p : Y ⟶ Spec A`, a field `F` with `IsFractionRing A F` gives the actual generic-fibre pullback and projection. `projection_stalkMap_isIso` and `stalkEquiv` identify actual local rings through that projection's own stalk map. The general `stalkMap_isIso_of_flat_of_surjectiveOnStalks` retains flatness and stalk-surjectivity hypotheses.

Focused imports are the two leaves. [Etale stalk comparison](../Morphisms/Etale/README.md) and [smooth regularity/dimension](../Morphisms/Smooth/README.md) consume the polynomial/local interfaces. The generic-fibre conclusion makes no global integrality claim about the original scheme.
