# Restriction generation from original section lifting

Import: `Aglib.AlgebraicGeometry.Modules.Generators.Restriction`.

For arbitrary schemes `E`, `X`, an actual morphism `i : E ⟶ X`, and an actual
module map `φ : F ⟶ M`,
`pullback_app_top_surjective_of_unit_app_top_surjective` derives surjectivity on
sections of `(pullback i).map φ` from surjectivity of `φ` and the original
adjunction unit at `M`. The proof evaluates the existing unit naturality square;
it introduces no replacement map or pullback model.

`epi_pullback_of_sections_and_unit_surjective` adds only epimorphy of the
original `globalSectionsEval ((pullback i).obj M)` and derives epimorphy of the
same pulled-back map. It reuses `exists_unitHom_factor_of_surjective` and
`epi_of_unitHom_factor`. No closed immersion, properness, finite type, rank-one
coefficient or Noetherian hypothesis is needed.

The intended canonical evaluation consumer supplies the unit-surjectivity
input from the existing localized exceptional canonical vanishing theorem.
Generation of the actual restricted canonical coefficient is a separate
obligation, not a consequence of this result.

## Verification

Native graph121 accepted the production leaf `449de76e` in 1.7 seconds at
the normal compiler settings. No existing supplier was changed. This result
proves only the stated original-map implication; it does not supply the
separate canonical generation premise.
