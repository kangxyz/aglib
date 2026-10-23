# Pullback of arbitrary-section nonvanishing opens

[Pullback.lean](Pullback.lean) keeps the original module sheaves and section maps.
`pullbackSection f M s` is the pullback-pushforward adjunction unit applied to
the actual global section `s : Γ(M, ⊤)`. Its target is the actual module
`(Scheme.Modules.pullback f).obj M`. It is not a section selected by a
nonvanishing condition or supplied through a compatibility premise.

`nonvanishingOpen_pullback` states that its nonvanishing open in the actual
`pullbackLineBundle f L` is `f ⁻¹ᵁ nonvanishingOpen L s`, for an arbitrary
scheme morphism `f` and actual line bundle `L`. There is no Noetherian,
quasi-compactness or flatness premise.

The construction transports actual over-site frames through `overFunctorEquiv`
and `overEquiv`. `frameOnRestriction_coefficient` retains the literal ring
comparison `appIso` and module comparison `restrictAppIso`.
`localPullbackIso_section` applies the existing `restrictedUnit` identity to
the original section. `pulledRestrictionFrame_coefficient` then computes its
actual pulled coefficient using adjunction naturality and
`pullbackUnitIso_homEquiv`. The geometric argument uses the actual
`preimage_basicOpen` formula and the original restricted morphism square.
The local-hom property of scheme stalk maps underlies this basic-open formula;
arbitrary ring maps would not justify reflecting units at original points.

`restrictSection` is the literal original restriction through `restrictAppIso`.
`restrictLineBundle` has the actual module `L.val.restrict f`, with its local
rank-one property transferred along the native `restrictFunctorIsoPullback`.
`restrictSection_to_pullback` uses the unit identity for that actual
left-adjoint comparison. `nonvanishingOpen_restrictLineBundle` therefore states
the equality on the original restricted scheme itself for any open immersion.

These are generic section and open identities. Tensor-section coefficients,
ampleness, relative quasi-projectivity and surface-contraction construction
are separate obligations. The passed parent nonvanishing and open-replacement
owners remain unchanged.
