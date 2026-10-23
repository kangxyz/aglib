# Finite local bases, exact pullback and rank

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic`, defines `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X M` from one actual local generating family which is a finite basis on every cover member. `FiniteLocallyFree X` is the full category. A finite local basis gives actual finite presentation with no relations and hence quasicoherence, on an arbitrary scheme.

[LocalBases](LocalBases.lean), [LocalSplitting](LocalSplitting.lean) and [Locality](Locality.lean) construct actual local bases, locally split epimorphisms onto finite locally free objects and open-local transport. Their finite simultaneous lifts come from [Generators](../Generators/README.md). [Exact](Exact.lean) gives `vectorBundleExactStructure`: actual short exact sequences with finite locally free ends have finite locally free middle. This is an exact category, not an asserted abelian category.

[Pullback](Pullback.lean) gives `vectorBundlePullback` and `vectorBundleExactPullback` for arbitrary scheme morphisms, using local splitting with vector-bundle quotient; no flatness hypothesis on the morphism is required. [Restriction](Restriction.lean) gives actual exact open restriction. Identity/composition/restriction comparisons are natural isomorphisms of the original functors. [Coherent](Coherent.lean) supplies the exact coherent inclusion under local Noetherianity.

[FiniteType](FiniteType.lean) proves `finite_globalSections_of_finiteLocallyFree` on an affine scheme over any commutative ring: global sections are finitely generated. This leaf proves finite generation. The newly admitted [Affine](Affine/README.md) family additionally proves finite presentation/projectivity of actual global sections and constructs finite-free retracts.

[FibreDimension](FibreDimension.lean) proves `Scheme.Modules.moduleFibre_finite_and_finrank_eq_card` for the actual scheme, local basis, field-valued point and chart: the fibre is finite dimensional, with dimension equal to the chart basis cardinality. It imports Basic and BaseChange.Basic below Rank, preserving the same universe and finite-index hypotheses.

[Rank](Rank.lean) uses the canonical class and this proved fibre theorem. `SheafFiniteLocallyFree` is an abbreviation; `isFiniteLocallyFree_iff_exists_localBasis` and `localGeneratorsData_isFiniteType_iff` compare it with the same explicit local-basis witness, and `SheafHasRank.isFiniteLocallyFree` supplies the class from a specified rank witness. Local constancy and geometric-point detection require no global theorem-family input. The wrappers `FiniteLocallyFree.rank`, `rank_locallyConstant`, `hasRank_iff_rank_eq` and `exists_hasRank` use the actual objects; connected constancy keeps `ConnectedSpace`, while geometric detection includes empty schemes.

The lower subjects are finite presentation, actual stalk/pullback/locality and exact subcategories. Coherent inclusion, differential rank and relative cohomology use these same class and witness interfaces. The fibre calculation has its own pointwise proof.

[Tensor](Tensor/README.md) owns exact left/right tensor and `PreservesHomology` for finite locally free coefficients, with affine/injective restriction conditions retained.

The general local-basis pushforward and binding declarations live in [module sheaves on arbitrary sites](../../../Algebra/Category/ModuleCat/Sheaf/LocallyFree/README.md), in namespace `SheafOfModules`. The scheme Restriction and Locality leaves specialize those actual cover, basis and finite-type witnesses.

[LocalLifting](LocalLifting.lean) converts the actual local splitting of a finite
locally free quotient into a section on an actual open subscheme. Maps from a
finite locally free sheaf lift locally through epimorphisms and factor locally
through an exact short complex, with the original restriction equations. These
statements do not assume that the sheaf is globally projective. They supply the
finite local correction step for strict-perfect chain nullhomotopies.

[FreeCover](FreeCover.lean) constructs actual local generating families from free presentations on an arbitrary open cover, retaining the cover and index types. Finite indices give finite local freeness; the fixed `ULift (Fin n)` basis gives `SheafHasRank`. Its isomorphism transport compares the same actual restricted/free objects. Smooth differential rank uses these constructions without a local-basis fibre-dimension assumption.

[FiniteFlat](FiniteFlat.lean) proves `Scheme.Modules.finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree`: for finite flat locally finitely presented `f`, its actual structure-module direct image is finite locally free on the original target. It uses native affine bases and iso/open-cover descent and creates no rank/degree or morphism-wrapper predicate.

[OpenImage](OpenImage.lean), imported as `Aglib.AlgebraicGeometry.Modules.LocallyFree.OpenImage`, transports an actual free presentation across an open immersion to the image open. Its generator index is arbitrary; no finiteness or rank-one hypothesis is imposed.

[KernelPullback](KernelPullback.lean): for an epimorphism `g : M ⟶ N` onto a finite locally free sheaf and any morphism `f`, `f^*(ker g)` is the kernel of `f^* g` (`pullbackKernelIsKernel`, `pullbackKernelIso`), with no flatness. Relocation candidate: `shortExact_kernelSequence` holds in any abelian category and belongs with Mathlib's `ShortComplex.kernelSequence`.

[Kernel](Kernel.lean): in a short exact sequence of module sheaves with finite locally free middle and last terms, the first term is finite locally free (`finiteLocallyFree_X₁_of_shortExact`; on `Spec R`, `finiteLocallyFree_X₁_of_shortExact_Spec`). The proof works on affine charts, where global sections are exact and the kernel's sections are a finite projective summand ([ProjectiveKernel](../../../Algebra/Category/ModuleCat/ProjectiveKernel.lean)).

[RankAdditivity](RankAdditivity.lean): fibre ranks add along a short exact sequence whose first and last terms are finite locally free, at every field-valued point (`finrank_moduleFibre_X₂_eq_add_of_shortExact`) and at every point (`sheafRank_X₂_eq_add_of_shortExact`); a finite free sheaf has rank its number of generators (`finrank_moduleFibre_free`, `sheafRank_free`).
