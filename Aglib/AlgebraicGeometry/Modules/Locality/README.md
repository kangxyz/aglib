# Detection on stalks and open covers

[Isomorphisms](Isomorphisms.lean), imported as `Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms`, gives `Scheme.Modules.moduleSheaf_isIso_iff_stalks` and the actual restriction/open-cover variants. A morphism is invertible when its genuine stalk maps are, with the original scheme/module objects.

[Exactness](Exactness.lean) detects zero objects, isomorphisms and short exact sequences through a jointly covering family of actual open immersions. [Monomorphisms](Monomorphisms.lean) detects monomorphisms from actual restrictions and gives the stated open-restriction/pullback comparison. Joint coverage or stalkwise premises remain inputs.

These three focused leaves feed coherent pullback, local splitting, affine/coherent gluing and exact module-functor arguments. The lower stalk/support and restriction functors are defined in [ambient Modules](../README.md), before any finiteness or Noetherian property is imposed.

[Sections](Sections.lean), imported as `Aglib.AlgebraicGeometry.Modules.Locality.Sections`, relates monicity to injectivity on actual module sections and detects equality on the affine basis. These are statements about arbitrary module sheaves, without quasicoherence or ideal hypotheses.

[AffineGluing](AffineGluing.lean) glues restriction-compatible sections
on all affine subopens and detects equality there, for arbitrary module sheaves.
It requires no quasicoherence, finiteness or completion hypothesis.

[ChartSections](ChartSections.lean) proves that the coefficient section map
on commuting open charts respects refinement of both chart images. It uses
the native restricted coefficient and module-presheaf maps, without a flatness,
quasicoherence or cartesian-square hypothesis.
