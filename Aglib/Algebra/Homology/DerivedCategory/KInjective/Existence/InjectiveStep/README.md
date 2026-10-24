# The functorial injective step

These leaves construct the concrete lower steps for the transfinite
K-injective existence route of [Stacks 079N](https://stacks.math.columbia.edu/tag/079N)
and [079P](https://stacks.math.columbia.edu/tag/079P). They use native
`CochainComplex`, `mappingCone`, `mappingCocone`, and cokernels throughout.

- `Objects.lean` extracts `CategoryTheory.IsGrothendieckAbelian.injectiveStepObjects`
  and its original mono natural transformation `injectiveStepObjectsι` from
  Mathlib's functorial monomorphism factorization. This functor is not asserted
  additive. The object, morphism and Grothendieck size universes are separate.
- `Contractible.lean` forms the zero-differential complex of these injectives
  and its native identity cone. `CochainComplex.injectiveStepContractibleUnit`
  is the natural monomorphism from the original complex; its two projection
  equations retain the actual injective embeddings and original differential.
  The target is termwise injective and has a specified null homotopy of its
  identity. This monomorphism is **not** a quasi-isomorphism in general.
- `Quotient.lean` forms the actual functorial cokernel and proves the defining
  sequence short exact. `injectiveStepConeComparison` is the original native
  quasi-isomorphism from the cone of the embedding to this cokernel, and
  `injectiveStepConeComparison_inr` preserves the actual quotient projection.
  `injectiveStepCoconeι` is the original augmentation to the mapping cocone
  of that quotient projection. It is monic, and each of its components factors
  through an actual injective subobject via `injectiveStepCoconeι_injectiveFactor`.

- `Naturality.lean` constructs `injectiveStepFunctor` as the original cone
  functor of the actual natural quotient projection followed by the native
  minus-one shift. `injectiveStepUnit` is the original natural monomorphism.
  Its chain-level naturality uses the generic `MappingCocone/Map.lean` supplier.
- `QuasiIso.lean` applies the generic `mappingCocone.quasiIso_liftShortComplex`
  to the genuine defining short exact sequence. The endpoint
  proves quasi-isomorphism of the original `injectiveStepUnit` and retains
  its original injective-subobject factorization. This augmentation theorem
  is distinct from the cone-to-quotient comparison in `Quotient.lean`.

## Exact remaining obligations

The coordinating compiler accepted the full `InjectiveStep.QuasiIso` import
closure in graph 018, including the actual augmentation quasi-isomorphism.
This compilation evidence does not assert final audit or full replacement
existence.

This is only the injective-factor
successor operation, not K-injective replacement. The set-sized bounded-above
acyclic family, its detection theorem with compatible transfinite homotopies,
the map-killing successor operation, and the transfinite AB5/smallness join
remain substantive separate foundations. No supplied-replacement predicate,
boundedness assumption, second model theory, or unbounded functor existence
claim is introduced here.

The contractible embedding adapts the actual cone-lift construction in
Mathlib `Algebra/Homology/Factorizations/CM5b.lean` by Joël Riou, replacing its
nonfunctorial individual embeddings by the native Grothendieck functorial
ones. It does not use a model-category structure or a bounded-below argument.
