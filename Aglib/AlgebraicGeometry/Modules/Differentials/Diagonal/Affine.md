# Affine diagonal conormal and native differentials

`Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal.Affine` defines the
canonical map `Diagonal.differentialToConormal p` from native relative
differentials to the actual pullback of the diagonal ideal. It is induced by
the literal coordinate difference `p₂* a - p₁* a` and the universal property
of the relative differential sheaf.

For every ring map `φ : R ⟶ A`,
`Diagonal.differentialToConormal_specMap_isIso` proves that the same map on
`Spec.map φ` is invertible. `Diagonal.conormalSpecIso φ` is its inverse
isomorphism. The affine tensor-kernel comparison carries
`1 ⊗ a - a ⊗ 1` to the original universal differential `D(a)`.
`Diagonal.algebraKaehlerIso` compares the native ring-map Kähler object
with the algebra Kähler module using equality of their algebra structures;
its generator formula preserves this same `D(a)`.

The affine comparison requires no smoothness, separation, finiteness,
reducedness, or field hypothesis. The source-open naturality and gluing
consumer is `Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal`.
