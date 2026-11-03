# Native affine pushforward section evaluation

`PushforwardSections.lean` imports only the existing `Pushforward` leaf and owns
`moduleSpecΓFunctor_map_pushforwardGlobalSectionsIso_apply`. The declaration,
including its `rfl` proof, is moved byte-for-byte from
`ChartPullbackCoordinateSections`; there is only one implementation.

For arbitrary `R S : CommRingCat.{u}`, `φ : R ⟶ S`, original module sheaves
`M`, `N`, a coefficient `q : M ⟶ (pushforward (Spec.map φ)).obj N` and an
original global section `m`, the native section comparison evaluates to
`q.app ⊤ m`. There is no quasicoherence assumption or replacement map.

The two direct consumers are `PresentationUnits` and
`ChartPullbackCoordinateSections`. Keeping this formula in a focused sibling
leaves the existing `Pushforward` source and its other import paths unchanged.
This is source-staged only; no new native acceptance or cost improvement is
asserted.
