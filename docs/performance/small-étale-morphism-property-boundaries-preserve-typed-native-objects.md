> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#small-étale-morphism-property-boundaries-preserve-typed-native-objects) · [Context](original-context.md) · [Case index](README.md) · [Previous record](original-represented-étale-cohomology-normalize-complete-values-before-specialization.md) · [Next record](typed-projection-proofs-across-additive-hom-carriers.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Small étale morphism-property boundaries: preserve typed native objects

The finite affine refinement producer failed in graphs001,004,006 and010 with
instance and implicit-transparency mismatches at the `Scheme.Etale` /
`MorphismProperty.Over` boundary. Printed morphism-property heads could look
identical while elaboration could not identify the expected native category.
Use the explicitly typed eta-expanded property
`fun {X Y : Scheme.{u}} (f : X ⟶ Y) => AlgebraicGeometry.Etale f`, and provide
the original-site category to constructors such as
`Presieve.ofArrows.mk (C := S.Etale)`. For a native Over factorization, typed
`congrArg` and `Eq.trans` avoid an unnecessary `calc` transitivity search through
projected carrier expressions. Reuse the actual covering and morphism-property
instances rather than inventing alternate site structures.

Graph014 accepted `EtaleAffineBasis.FiniteRefinement` in2.0 seconds and
`FiniteHypercovers` in2.2 seconds with these repairs. These are full-leaf native
build times, not isolated benchmarks. No heartbeat or linter relaxation, test,
audit or kernel replay was used. The later qcqs hypercover consumer remains a
separate compilation obligation.

