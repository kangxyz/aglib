# Affine presentation maps and their units

[AffineFunctor](AffineFunctor.lean) transports a presented map through a
square of functors between arbitrary categories. Its composition law uses
the given natural comparison square and actual intermediate presentation
isomorphism; the final target presentation may be a morphism.

[AffineSheaf](AffineSheaf.lean) applies that construction to the original
affine tilde and scalar-extension comparisons.
[AffineSheafUnit](AffineSheafUnit.lean) evaluates the resulting map on the
geometric pullback unit: a presented section at `x` maps to the target
presentation at `t(1 ⊗ x)`. The target presentation need not be invertible
and the target sheaf need not be quasicoherent.
These are equations of the original maps, with no flatness premise.

Present consumers include [The actual nonflat higher-image comparison over affine bases](Affine.lean), [Coefficient naturality of the native nonflat affine comparison](AffineNaturality.lean).
