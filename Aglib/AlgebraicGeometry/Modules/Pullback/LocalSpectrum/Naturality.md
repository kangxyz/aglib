# Original local-spectrum comparisons are natural

`Naturality.lean` organizes the existing component isomorphisms from
`Modules/Stalk/LocalSpectrum` and `Modules/Pullback/LocalSpectrum` into natural
isomorphisms. The component normalization theorem identifies the forward map
with the original `stalkFromSpecStalkSectionsIso`, not an independently chosen
same-endpoint isomorphism.

For any ordinary morphism f:M→N, the exact equation is

    stalk(f) ; stalkSections_N
      = stalkSections_M ; GammaSpec(pullback(f)).

The proof composes naturality of the scalar-extension adjunction unit, the
existing pullback/stalk isomorphism, and the original closed-point germ. The
local ring's closed-point identification and scalar action are unchanged.
There is no quasicoherence, finite-type, Noetherian or properness hypothesis.

The immediate consumer is the q=0 ordinary-direct-image localization formula
for the actual proper canonical trace. This lower module imports no cohomology
provider and constructs no second module-sheaf or derived-category model.
Native compiler evidence remains the integrator's responsibility.
