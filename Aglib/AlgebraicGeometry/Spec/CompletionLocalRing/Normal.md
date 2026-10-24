# Normal completion from an actual proper regular model

`Normal.lean` assumes a Noetherian local base B, an actual proper morphism
`p : Z → Spec B`, regularity of its source stalks, and bijectivity of the
literal structural map
`p.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom`.
It proves that the same maximal-ideal `AdicCompletion` is a domain and is
integrally closed. The local-ring interface includes nontriviality.

`bijective_structuralSections_of_flat_baseChange` derives bijectivity of
the original structural section map on an actual flat fibre product. Its
map is the existing `moduleCohomologyTensorMap` in degree zero with the
original pullback-unit coefficient arrow. Flat base change supplies its
invertibility, and the existing `pullbackUnitSections` uses the original
`pullbackUnitIso` to identify the actual coefficient. The native pure-tensor
formula and original H0 normalization show that the resulting equivalence
sends every scalar to its literal structural section. Bijectivity is
therefore proved for the original ring
homomorphism; no unspecified section-ring isomorphism is a premise.

For completion, `completionStructuralSectionsEquiv` has precisely that
structural ring map as its forward map. The existing
`regularStalks_completionBaseChange_iff` proves regularity of the actual
completed pullback. Its global ring is local and nonzero, hence the source
is nonempty and connected. Regular stalks give normal stalks, and the
existing locally Noetherian connected-normal theorem gives integrality.
Only then are the domain and integral-closedness properties of its global
ring transported back to the completion.

In particular, no domain property of the completion is used to prove its
connectedness or normality. There is no dimension, Nagata, excellence,
coefficient-field, J-2, formal-functions, GR, or resolution-existence
assumption. The [Necessity](../../Surfaces/Resolution/Necessity.md) consumer
derives the intermediate structural bijection from its supplied proper
birational normal factor. It is not a premise of that final necessity
implication. The present module supplies the local completion argument;
the finite singular set and the global necessity assembly belong to that
consumer.
