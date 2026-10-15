# Cochain complexes and augmentations

The focused imports `Aglib.Algebra.Homology.CochainComplex.KernelSequence`, `.DegreewiseSplitMono` and `.SingleShift` extend actual `CochainComplex A ℤ` in an arbitrary abelian category. Object and morphism universes remain independent where the source supplies them.

[KernelSequence](KernelSequence.lean) constructs `CochainComplex.kernelSequence K n`: the inclusion of the kernel of the differential at `n`, followed by the differential lifted to the next kernel. `kernelSequence_shortExact` assumes `K.ExactAt (n + 1)` and proves this actual sequence short exact. It does not require an injective resolution or acyclicity in every degree.

[DegreewiseSplitMono](DegreewiseSplitMono.lean) defines `CochainComplex.degreewiseSplitMono f` by a splitting of each component `f.f n`. It proves that these maps are monomorphisms, contain isomorphisms and maps from zero complexes, and are stable under composition and actual pushouts. The component splittings need not form a chain retraction. Its lower `CategoryTheory.Limits.IsPushout.isSplitMono_inr` works in any category from a chosen pushout square and a split first input.

[SingleShift](SingleShift.lean) proves `CochainComplex.chainMap_single_zero_to_shift_one_eq_zero`: a cochain map from a degree-zero single to the shift by one of another degree-zero single is zero. The source retains its actual shift convention and abelian coefficient category.

[Augmentation](Augmentation.lean), imported as `Aglib.Algebra.Homology.CochainComplex.Augmentation`, owns `CochainComplex.quasiIsoAtZero_of_augmentation_exact`. In an arbitrary abelian category, take an actual augmentation from a degree-zero single to an ℕ-indexed cochain complex. If its degree-zero component is monic and the augmented short complex in degrees zero and one is exact, the map is a quasi-isomorphism at degree zero. The conclusion concerns that degree; no higher-degree acyclicity is assumed or supplied. The scheme Cech comparison is a consumer of this category-generic criterion.

The [stupid truncation layers](../Embedding/StupidTrunc/README.md) use degreewise splitting. The [flasque complex calculation](../../../AlgebraicGeometry/Cohomology/Flasque/README.md) uses kernel sequences and cone acyclicity. These generic complex interfaces precede their scheme-specialized consumers.
