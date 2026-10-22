# Closed-pullback and complement detection of epimorphisms

The native endpoint
`Scheme.Modules.epi_of_pullback_closedImmersion_of_stalkFinite i φ hN hoff`
concerns the original closed immersion `i : E ⟶ X` and original map
`φ : M ⟶ N` of actual `X.Modules`. It proves `Epi φ` from:

- the actual instance `Epi ((Scheme.Modules.pullback i).map φ)`;
- `hN : ∀ y : E, Module.Finite (X.presheaf.stalk (i y))
  ((Scheme.Modules.moduleStalk X (i y)).obj N)`;
- `hoff : ∀ x : X, x ∉ Set.range i →
  Epi ((Scheme.Modules.moduleStalk X x).map φ)`.

The source module is arbitrary. Finiteness is required only for target stalks
on the image, and no quasicoherence, coherence, Noetherianity, flatness or field
hypothesis is added. The variant
`epi_of_pullback_closedImmersion_of_stalkSurjective` takes literal surjectivity
of those original off-image stalk maps instead of categorical epimorphy.
Both endpoints retain the original modules, map, pullback and stalk actions.

At an image point `i y`, the existing `pullbackModuleStalkIso i y` identifies
the actual pulled map with scalar extension of the original stalk map along
the original structure-sheaf stalk homomorphism. That comparison needs no
flatness hypothesis. The closed immersion makes this ring map surjective.
Its proper kernel lies in the maximal ideal of the local source stalk ring,
and hence in its Jacobson radical.

The finite-target algebra argument uses existing scalar descent along a
surjective ring map, applied to the original target modulo its kernel times
the target. The original scalar adjunction and its surjective unit show that
the original map is onto this quotient. Native
`LinearMap.surjective_of_surjective_comp_mkQ` then gives surjectivity of the
original map by Nakayama. This uses no finiteness of the source and creates no
replacement stalk or tensor interface. Finally `epi_of_moduleStalk` combines
the image and complement conclusions.

The consumer still owns proofs that its actual closed-pullback map is epi,
that its target stalks have the indicated finite actions, and that the
original map is epi off the image. These are explicit inputs, not generation
or desired-epimorphism oracles hidden inside another model.
