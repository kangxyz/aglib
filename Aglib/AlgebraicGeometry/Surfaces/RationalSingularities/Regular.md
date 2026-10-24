# Regular local surfaces and universal model cohomology

`Scheme.RationalSingularities.NormalModificationH1Vanishing A` means that
every actual integral normal scheme with an actual proper dominant map
to `Spec A` and invertible original function-field map has zero original
structure-module H1. This is a universal property of the original models;
it does not use a chosen resolution or a projective-only model convention.

`normalModificationH1Vanishing_of_regularLocal` proves this property for
the original regular local ring of dimension two. The native regular-local
interface supplies Noetherianity and locality, and the proof derives the
domain instance, normality and regularity of the actual affine source.
No field, trait, Nagata or completeness hypothesis is imposed. In the
[Stacks rational-singularity definition, 54.8.3](https://stacks.math.columbia.edu/tag/0B4N)
the Nagata domain of definition is retained separately; this predicate
does not imply Nagata.

For each supplied `f : Y → Spec A`, form the actual generic inverse
from the inverse of the original `functionFieldMap f` and the literal
generic-point stalk morphism of `Y`. The existing regular-source common
domination theorem constructs an original finite point-blowup chain
`β : Z → Spec A` and an actual proper surjective `h : Z → Y`, retaining
`h ≫ f = β` and the original generic triangles. It requires regularity
of the original affine source and does not assume regularity or
projectivity of `Y`. The original field-map composition then proves
birationality of this same `h`.

The private chain argument uses only exactness at the middle term of the
original `moduleBirationalLerayShortComplex`. Its source H1 is zero by
induction. The actual first higher direct image of a regular point
blowup is zero by [RegularPoint](../../Cohomology/Blowup/RegularPoint.md),
so the native edge isomorphism makes the third term zero. Exactness
makes the middle term zero, and the actual middle cohomology equivalence
gives zero original H1 on the next chain source. The initial affine H1
is zero. No H2 bound or full short exact Leray sequence is used.

The original proper-birational unit gives an injection from H1 of the
supplied normal `Y` into H1 of this actual `Z`, through the injection-only
interface and its original cohomology-map normalization.
The target is zero by the same chain induction. This concludes the
universal vanishing property before any general surface resolution
theorem.

This is universal vanishing over an already regular local base.
Resolution of an initially singular surface, and the full RES and RES-QE
existence statements, remain open.
