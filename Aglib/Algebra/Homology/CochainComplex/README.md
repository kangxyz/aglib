# Cochain complexes and augmentations

The focused imports `Aglib.Algebra.Homology.CochainComplex.KernelSequence`, `.DegreewiseSplitMono` and `.SingleShift` extend actual `CochainComplex A ℤ` in an arbitrary abelian category. Object and morphism universes remain independent where the source supplies them.

[KernelSequence](KernelSequence.lean) constructs `CochainComplex.kernelSequence K n`: the inclusion of the kernel of the differential at `n`, followed by the differential lifted to the next kernel. `kernelSequence_shortExact` assumes `K.ExactAt (n + 1)` and proves this actual sequence short exact. It does not require an injective resolution or acyclicity in every degree.

[Cycles](Cycles.lean) owns `CochainComplex.shortExact_cycles`: the native
sequence `K.cycles n → K.X n → K.cycles (n+1)` is short exact when the
original complex is exact in degree `n+1`. The arrows are the original
`iCycles` and `toCycles`. This theorem has no flatness, projectivity,
finiteness or boundedness premise. Its sole implementation was extracted
unchanged from `FiniteProjective.Cycles`, which imports this lower owner
and retains the same declaration name for existing consumers. The lower
leaf passed with receipt `1792096965456898000-23506`, followed by its
changed finite-projective consumer with receipt `1792097031365973000-25172`.

[DegreewiseSplitMono](DegreewiseSplitMono.lean) defines `CochainComplex.degreewiseSplitMono f` by a splitting of each component `f.f n`. It proves that these maps are monomorphisms, contain isomorphisms and maps from zero complexes, and are stable under composition and actual pushouts. The component splittings need not form a chain retraction. Its lower `CategoryTheory.Limits.IsPushout.isSplitMono_inr` works in any category from a chosen pushout square and a split first input.

[SingleShift](SingleShift.lean) proves `CochainComplex.chainMap_single_zero_to_shift_one_eq_zero`: a cochain map from a degree-zero single to the shift by one of another degree-zero single is zero. The source retains its actual shift convention and abelian coefficient category.

[Augmentation](Augmentation.lean), imported as `Aglib.Algebra.Homology.CochainComplex.Augmentation`, owns `CochainComplex.quasiIsoAtZero_of_augmentation_exact`. In an arbitrary abelian category, take an actual augmentation from a degree-zero single to an ℕ-indexed cochain complex. If its degree-zero component is monic and the augmented short complex in degrees zero and one is exact, the map is a quasi-isomorphism at degree zero. The conclusion concerns that degree; no higher-degree acyclicity is assumed or supplied. The scheme Cech comparison is a consumer of this category-generic criterion.

The [stupid truncation layers](../Embedding/StupidTrunc/README.md) use degreewise splitting. The [flasque complex calculation](../../../AlgebraicGeometry/Cohomology/Flasque/README.md) uses kernel sequences and cone acyclicity. These generic complex interfaces precede their scheme-specialized consumers.

[HomologyZero](HomologyZero.lean) gives the native embedding
`CochainComplex.homologyZeroι K : K.homology 0 ⟶ K.X 0` for natural-number
cochain complexes in an abelian category. It is monic and natural in actual
complex maps. Exact additive functors preserve this embedding through the
native homology comparison. An augmentation from a degree-zero single retains
its literal zero component under the embedding. The native identity
`homologyπ_homologyZeroι` states that the original cycle quotient followed
by the embedding is exactly the original cycle inclusion; it passed the
focused owner build `1792099006611075000-66323`. The scalar-compatible
[Cech degree-zero computation](../../../AlgebraicGeometry/Cohomology/Cech/DegreeZero/Forget.lean)
uses these equations to identify original section and geometric maps.

[MapTruncation](MapTruncation.lean) gives
`CochainComplex.mapTruncLEIso K F b`, the actual isomorphism between
`F(K.truncLE b)` and the native upper truncation of `F(K)`. The coefficient
categories are arbitrary abelian categories with independent object and
morphism universes. The functor need only preserve zero morphisms and the
original boundary kernel of `K.d b (b + 1)`; no global exactness or homology
preservation is assumed. The boundary isomorphism is the native unique
comparison of the preserved kernel forks. The original term isomorphisms and
zero terms supply the remaining components.

`mapTruncLEIso_hom_ιTruncLE` retains the actual inclusion: the comparison followed
by the target's original truncation inclusion is precisely the functor's image
of the original source inclusion. `mapTruncLEIso_hom_naturality` retains every
coefficient chain map when the two displayed boundary kernels are preserved.
`quasiIso_map_ιTruncLE_of_isLE` proves that this original mapped inclusion is a
quasi-isomorphism under the actual upper cohomological bound on `F(K)`.
The native truncation/projection and cycle-inclusion equations are also exposed.
The current consumer supplies boundary kernel preservation through universal
tensor exactness and actual flat image/cokernel modules, below geometric base change.

The MapTruncation leaf was compiled alone through the shared serialized wrapper,
receipt `1792088726964846000-53888`.
The external `work/proper-validation/MapTruncationConsumer.lean` checks the
native objects, actual inclusion equation, coefficient naturality and mapped
inclusion quasi-isomorphism under only the displayed kernel and upper-bound
hypotheses. It passed with receipt `1792089027310637000-63256`; the inspected
comparisons use only `propext`, `Classical.choice` and `Quot.sound`.

[BaseChangeCriterion](BaseChangeCriterion.lean) proves
`free_homology_iff_epi_residue_predecessor` for the original integer
cochain complex over a commutative local ring. Assume its degree-`i`
residue-field homology mate is surjective. The original `H^i` is free
exactly when the original degree-`i - 1` mate is surjective. Only the three
neighboring terms are finite and the last two are flat; boundedness and
Noetherianity are not required. The proof uses the native opcycles and
their original cokernel universal property. The independent public
consumer checks all integer degrees and ring/carrier universes with only
the standard three axioms.

[Grauert](Grauert.lean) proves the reduced-local constant-rank criterion
for original cochain homology. Local constancy of the actual residue-field
homology dimension makes original homology free and the unchanged native
mate invertible after every ring map. Only the present term is finite and
the next term finite flat; no bound or Noetherianity is required. The
independent all-universe consumer passed `1792103699120087000-50220`,
with only the three standard axioms.
