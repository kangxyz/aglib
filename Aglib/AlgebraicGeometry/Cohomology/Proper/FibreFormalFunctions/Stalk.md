# Idempotents in the image of the ordinary stalk-to-fibre map

The main endpoint in `FibreFormalFunctions/Stalk.lean` is
`ProperFibreFormalFunctions.exists_stalk_restrict_eq_of_isIdempotentElem`.
For an actual proper morphism `f : X ⟶ Y`, a locally Noetherian target, a
point `y : Y`, and an idempotent `e` in the global functions of the literal
scheme-theoretic fibre `f.fiber y`, it gives an element of the ordinary ring
stalk `(f.base _* X.presheaf).stalk y` whose image under
`ProperFibreIdempotents.stalkToFibreSections f y` is `e`.

The preimage is arbitrary. No idempotence of that original element, flatness of
`f`, Henselian or completeness hypothesis, geometric connectedness, effectivity
premise, or supplied compatible lifting family is part of the statement.

The proof has two comparisons with original maps. First,
`ordinaryStalkLocalSectionsEquiv` identifies the underlying additive group of
the original pushforward ring stalk with the global functions on the actual
pullback of `f` along `Y.fromSpecStalk y`. It composes the canonical additive
forgetful comparison of filtered stalk colimits, the native module-stalk/local
sections isomorphism, the actual ordinary Cartesian base-change map, the
pushforward global-sections comparison, and the original pullback-unit
isomorphism. Invertibility of the ordinary mate follows from the native
higher-direct-image flat base-change isomorphism and its proved degree-zero
unit square. The change of base `fromSpecStalk` is flat by the native theorem;
this introduces no hypothesis on the final morphism `f`.

`ordinaryStalkLocalSectionsEquiv_germ` identifies the forward map on every
original neighbourhood germ with literal restriction along the first pullback
projection. Its proof retains the actual point and scalar transports in the
native pullback-stalk isomorphism, the original scalar-extension unit, and the
actual Cartesian mate unit. It does not substitute an unspecified isomorphism
between the same two objects.

Second, `localFibreIso` is the native pullback-pasting isomorphism from the
maximal-ideal thickening of the local-spectrum source to the original fibre.
`localFibreIso_hom_fiberι` records its original first-projection triangle.
Together with the germ formula for the original stalk-to-fibre arrow, this gives
`localRestriction_stalkToFibreSections`, the required equality of the actual
restriction maps on every stalk element.

The final image statement then applies the fixed arbitrary-ideal affine theorem
`exists_section_restrict_eq_of_isIdempotentElem` to the proper local-spectrum
source. Its base ring is Noetherian because `Y` is locally Noetherian. Transport
of the given idempotent uses the actual fibre-isomorphism ring map; only the
arbitrary preimage is transported through the additive equivalence. Cancelling
the fibre-isomorphism ring map proves the original beta equation.
