# Finite local bases, exact pullback and conditional rank

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic`, defines `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X M` from one actual local generating family which is a finite basis on every cover member. `FiniteLocallyFree X` is the full category. A finite local basis gives actual finite presentation with no relations and hence quasicoherence, on an arbitrary scheme.

[LocalBases](LocalBases.lean), [LocalSplitting](LocalSplitting.lean) and [Locality](Locality.lean) construct actual local bases, locally split epimorphisms onto finite locally free objects and open-local transport. Their finite simultaneous lifts come from [Generators](../Generators/README.md). [Exact](Exact.lean) gives `vectorBundleExactStructure`: actual short exact sequences with finite locally free ends have finite locally free middle. This is an exact category, not an asserted abelian category.

[Pullback](Pullback.lean) gives `vectorBundlePullback` and `vectorBundleExactPullback` for arbitrary scheme morphisms, using local splitting with vector-bundle quotient; no flatness hypothesis on the morphism is required. [Restriction](Restriction.lean) gives actual exact open restriction. Identity/composition/restriction comparisons are natural isomorphisms of the original functors. [Coherent](Coherent.lean) supplies the exact coherent inclusion under local Noetherianity.

[FiniteType](FiniteType.lean) proves `finite_globalSections_of_finiteLocallyFree` on an affine scheme over any commutative ring: global sections are finitely generated. This leaf proves finite generation. The newly admitted [Affine](Affine/README.md) family additionally proves finite presentation/projectivity of actual global sections and constructs finite-free retracts.

[Rank](Rank.lean) uses this canonical class. `SheafFiniteLocallyFree` is an abbreviation; `isFiniteLocallyFree_iff_exists_localBasis` and `localGeneratorsData_isFiniteType_iff` compare it with the same explicit local-basis witness, and `SheafHasRank.isFiniteLocallyFree` supplies the class from a specified rank witness. Every substantive fibre/rank theorem retains `LocalBasisFibreDimension`: actual finite local bases give finite field fibres of their basis dimension. Conditional local constancy and geometric-point detection then apply. The wrappers `FiniteLocallyFree.rank`, `rank_locallyConstant`, `hasRank_iff_rank_eq` and `exists_hasRank` use the actual objects; connected constancy keeps `ConnectedSpace`, while geometric detection includes empty schemes.

The lower subjects are finite presentation, actual stalk/pullback/locality and exact subcategories. Coherent inclusion, differential rank and relative cohomology use these same class/witness interfaces; the category structure does not supply the explicit fibre-dimension family.

[Tensor](Tensor/README.md) owns exact left/right tensor and `PreservesHomology` for finite locally free coefficients, with affine/injective restriction conditions retained. These results still do not supply `LocalBasisFibreDimension`.

The general local-basis pushforward and binding declarations live in [module sheaves on arbitrary sites](../../../Algebra/Category/ModuleCat/Sheaf/LocallyFree/README.md), in namespace `SheafOfModules`. The scheme Restriction and Locality leaves specialize those actual cover, basis and finite-type witnesses.

[LocalLifting](LocalLifting.lean) converts the actual local splitting of a finite
locally free quotient into a section on an actual open subscheme. Maps from a
finite locally free sheaf lift locally through epimorphisms and factor locally
through an exact short complex, with the original restriction equations. These
statements do not assume that the sheaf is globally projective. They supply the
finite local correction step for strict-perfect chain nullhomotopies.
