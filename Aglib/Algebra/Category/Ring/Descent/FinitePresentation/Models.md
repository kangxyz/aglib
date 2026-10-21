# Finitely presented algebra models

Import `Aglib.Algebra.Category.Ring.Descent.FinitePresentation.Models`.

For a small filtered category `I`, a diagram `F : I ⥤ CommRingCat`, and an
actual colimit cocone `c` with proof `IsColimit c`,
`CommRingCat.exists_finite_subset_range_ι_app` lifts any finite set of
coefficients to one common stage. No transition or cocone map is required to
be injective.

`Algebra.Presentation.exists_model_of_isColimit` applies that result to the
coefficients of the relations in a finite presentation of the original
algebra `A`. Its witness is Mathlib's `Presentation.ModelOfHasCoeffs`, and its
comparison is Mathlib's `tensorModelOfHasCoeffsEquiv`. It also returns model
generators whose images are the specified generators of the presentation.

`Algebra.FinitePresentation.exists_model_of_isColimit` chooses a finite
presentation and returns an actual finitely presented `F.obj i`-algebra `B`
and an isomorphism `c.pt ⊗[F.obj i] B ≃ₐ[c.pt] A`. The tensor product uses
exactly the algebra structure induced by `c.ι.app i`.

The category, its hom types, and the coefficient rings share universe `u`;
the original algebra may lie in an independent universe `v`, while the model
is in universe `u`. This follows the native filtered-colimit forgetful
functor instance. The intended consumer is finite-stage affine scheme
descent. General scheme gluing and finite-diagram descent are separate
obligations.

The implementation extends Mathlib at revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, specifically
`Algebra/Category/Ring/FilteredColimits.lean` and
`RingTheory/Extension/Presentation/Core.lean`. It constructs the model from
the supplied colimit and presentation, without an assumed family of models.
