# The actual regular replacement tower

The construction follows Stacks 079P using only native objects and maps.

1. `Successor` composes the genuine injective-factor functor with the genuine
   all-maps attachment functor. The original natural unit remains mono/QI,
   kills original test maps, and factors termwise through injective subobjects.
2. `Iteration` uses native `SmallObject.SuccStruct.ofNatTrans` in the endofunctor
   category. This is generic transfinite recursion, not a second model theory.
   `Maps` supplies actual transition/cocone monicity from native Grothendieck
   stability under transfinite composition.
3. `Cardinal` constructs one regular cardinal bounding the separator's
   subobjects and every prescribed test complex's subobjects. Its ordinal
   index is small, cardinal-filtered, and has no maximal stage.
4. `Stages` retains the original successor equations, nullhomotopies, and
   injective factorizations inside the actual tower.
5. `InjectiveColimit` and `TestColimit` apply the native Grothendieck
   regular-cardinal map-factorization theorem to those actual diagrams.
   The native generator lifting criterion proves termwise injectivity.
6. `RegularStage` assembles the actual uniform endofunctor and original unit,
   with termwise injectivity and test nullhomotopies as conclusions, not inputs.

The index universe and category/hom universes remain independent. No arbitrary
inverse-limit exactness or assumed replacement provider is introduced.

7. `QuasiIso` transports the original pointwise successor QI through native
   transfinite composition, using the generic exact-colimit QI supplier.
8. `Replacement` specializes to the constructed small acyclic test family and
   applies the actual detection theorem. The chosen separator remains explicit.

The full `Replacement` endpoint was accepted and captured in compiler graph
093. Its original functor and natural augmentation are constructed without a
replacement premise. `Stages` and `RegularStage` were accepted in 092,
`QuasiIso` and `Replacement` in 093. The underlying exact-colimit supplier and
property wrapper were accepted in 089/091, the native detector in 083.

The public endpoint is `CochainComplex.kInjectiveReplacementFunctor hG` and
`kInjectiveReplacementUnit hG`, where `hG : IsSeparator G`. Instances prove the
original unit components monic and quasi-isomorphic, each target term injective,
and each target complex native `IsKInjective`. The functor is not assumed
additive. Derived-functor consumers retain this actual original augmentation.
