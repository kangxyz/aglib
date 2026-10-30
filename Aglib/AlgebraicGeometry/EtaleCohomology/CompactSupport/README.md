# Compactly supported étale cohomology along an open immersion

This family defines compactly supported cohomology for an open immersion `j : U ⟶ X` of schemes
in `Scheme.{u}` as the original cohomology of the extension by zero, with coefficients
`AbelianSheaf.{u, u + 1}` on the actual small étale sites. Its declarations belong to
`AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport`, except the three extension-by-zero
comparisons of [OpenLocalization](OpenLocalization.lean)
(`etaleLowerShriek_counit_directImage_isIso_of_range_subset`, `inverseImageDirectImageCompIso`,
`etaleLowerShriekDirectImageIso`), which are in `AlgebraicGeometry.Scheme.EtaleCohomology`. Ext
universes are explicit and independent (`w` on `X`, `w'` on a closed part or finite point
scheme); `HasExt` is a size hypothesis.

## Definition and long exact sequences

[Cohomology](Cohomology.lean) defines the `abbrev` `H j F r := Sheaf.H ((etaleLowerShriek j).obj F) r`
for `[IsOpenImmersion j]`; the equation with `Sheaf.H` holds by `rfl`. This is
`H^r_c(U, F) = H^r(X, j_! F)` of Milne, *Lectures on Étale Cohomology* v2.21, p. 92, for an
arbitrary ambient `X`; independence of `X` is not asserted. `H.map` is `Sheaf.H.map` of the
extended morphism, `functor j r` is `etaleLowerShriek j ⋙ Sheaf.functorH _ r`, and
`counitMap j G r : H^r_c(U, j^* G) → H^r(X, G)` is `Sheaf.H.map` of the original counit of
`etaleLowerShriekAdjunction j`. For a short exact sequence `S` on `U`, `δ`, `longSequence`,
`longSequence_exact`, `exact_map_f_map_g`, `exact_map_g_δ` and `exact_δ_map_f` form the original
`Sheaf.H` long exact sequence of the extended sequence `shortExact_etaleLowerShriek j hS`.

[Localization](Localization.lean) takes a closed immersion `i : Z ⟶ X` with
`Set.range j = (Set.range i)ᶜ`. The long exact sequence `localizationSequence` of
`abelianLocalization_shortExact` (Stacks, Tag 095L) has the original counit, the original unit of
`inverseImageAdjunction i` and the original connecting map `localizationδ`;
`localizationSequence_exact`, `exact_counitMap_unitMap`, `exact_unitMap_localizationδ` and
`exact_localizationδ_counitMap` state its exactness, and `counitMap_zero_injective` its
degree-zero injectivity.

## Finite closed complement

[FiniteComplement](FiniteComplement.lean) shows that vanishing of `H^r(X, i_* i^* G)` for all
`r > 0` makes `counitMap` surjective in positive degree and bijective for `r ≥ 2`
(`counitMap_surjective_of_subsingleton`, `counitMap_injective_of_subsingleton`,
`counitMap_bijective_of_subsingleton`). Let `D` be a finite set (`hfin`) of closed points
(`hclosed`) of `X` with separably closed residue fields (`hsep`), `i =
FiniteClosedSupport.inclusion X D` and `Set.range j = Dᶜ`. Through
`Finite.finiteCohomologyDirectImageAddEquiv` and `FiniteClosedSupport.subsingleton_H`,
`subsingleton_H_directImage_inclusion_of_sepClosed` gives `H^r(X, i_* M) = 0` for every `M` on
`pointScheme X D` and every `r > 0` (Milne, loc. cit., proof of Prop. 14.5, p. 92). Hence
`counitMap_bijective_of_finite_of_sepClosed` and `counitAddEquiv` for `r ≥ 2`, and
`counitMap_one_surjective_of_finite_of_sepClosed`; `counitMap_zero_injective_of_finite` needs no
`hsep`. With `pointRestriction` (original unit, then the finite comparison) and `pointBoundary`
(inverse comparison, then `localizationδ`), `exact_counitMap_pointRestriction`,
`exact_pointRestriction_pointBoundary` and `exact_pointBoundary_counitMap` hold in every degree
and give the exact sequence
`0 → H^0_c(U, j^* G) → H^0(X, G) → H^0(pointScheme X D, i^* G) → H^1_c(U, j^* G) → H^1(X, G) → 0`.
No finiteness, torsion or constructibility condition on `G` is imposed.

## Removing points

[PointRemoval](PointRemoval.lean) takes open immersions `jV : V ⟶ U` and `jU : U ⟶ X`, a set `D`
as above with `Set.range (jV ≫ jU) = Dᶜ`, and `F` on `U`. `restrictionExtensionIso` identifies
`(jV ≫ jU)^* (j_{U!} F)` with `jV^* F` through `inverseImageComp` and the inverse of the original
extension-by-zero unit (Stacks, Tag 0F70). `extensionMap` and `pointRemovalShortComplex` form the
short exact sequence `0 → j_{V!}(F|_V) → j_{U!} F → i_* i^* (j_{U!} F) → 0`
(`pointRemoval_shortExact`), isomorphic to the open-closed sequence of `j_{U!} F` for `jV ≫ jU` and
`i`. Its long exact sequence `pointRemovalSequence` has the maps
`extensionCohomologyMap : H^r_c(V, F|_V) → H^r_c(U, F)` and `pointRemovalδ`, with three exactness
theorems and `extensionCohomologyMap_zero_injective`. With `hsep`, the third term is acyclic in
positive degree (`subsingleton_H_pointRemoval_third_of_sepClosed`), so
`extensionCohomologyMap_surjective_of_sepClosed` holds for `r > 0`, and
`extensionCohomologyMap_bijective_of_sepClosed` and `extensionCohomologyAddEquiv` hold for
`r ≥ 2`. `pointRemovalBoundary` and the low-degree exactness theorems give the degree-zero/one
sequence through `pointScheme X D`. The third term is `i_* i^* (j_{U!} F)` on the whole support
`X − V`; its identification with the points of `U − V` is not formalized. The sequence on `U` of
Milne, loc. cit., Thm 14.7, proof, Step 2, p. 94, with third term on the points of `U − V`, is
that of [OpenLocalization](OpenLocalization.lean) below; both sequences have the first map
`extensionCohomologyMap`.

## The open-closed sequence on an open subscheme

[OpenLocalization](OpenLocalization.lean) takes open immersions `jV : V ⟶ U`, `jU : U ⟶ X`, a
closed immersion `i : Z ⟶ U` with `Set.range jV = (Set.range i)ᶜ` such that `i ≫ jU` is a closed
immersion, and `F` on `U`, and uses the long exact sequence of compactly supported cohomology
along `jU` of the original sequence `0 → jV_! jV^* F → F → i_* i^* F → 0` on `U`
(`abelianLocalization_shortExact`, Stacks, Tag 095L). Its terms are identified on the original
maps. `lowerShriekAddEquiv : H^q_c(U, jV_! A) ≃+ H^q_c(V, A)` is `Sheaf.H` of the inverse of
`etaleLowerShriekCompIso`; under it `H.map` of the counit `jV_! jV^* F ⟶ F` is the
`extensionCohomologyMap` of [PointRemoval](PointRemoval.lean) (`extensionMap_eq_compIso_counit`,
`extensionCohomologyMap_eq_map_counit`). `directImageAddEquiv : H^q_c(U, i_* M) ≃+ H^q(Z, M)` is
`Sheaf.H` of `etaleLowerShriekDirectImageIso : jU_! ∘ i_* ≅ (i ≫ jU)_*` (Stacks, Tag 0GJ1, for
the cartesian square of `i ≫ jU` and `jU`), followed by the finite direct-image comparison. That
isomorphism is `jU_!` of the inverse of `inverseImageDirectImageCompIso : jU^* ∘ (i ≫ jU)_* ≅ i_*`
followed by the original counit of `jU_! ⊣ jU^*`, which is invertible at `(i ≫ jU)_* M`
(`etaleLowerShriek_counit_directImage_isIso_of_range_subset`; Stacks, Tag 0F70, second
statement). With `compactRestriction` and `compactBoundary` the sequence
`… → H^r_c(V, F|_V) → H^r_c(U, F) → H^r(Z, i^* F) → H^{r+1}_c(V, F|_V) → …` is exact
(`exact_extensionCohomologyMap_compactRestriction`, `exact_compactRestriction_compactBoundary`,
`exact_compactBoundary_extensionCohomologyMap`), and its first map is injective in degree zero
(`extensionCohomologyMap_zero_injective_of_closedImmersion`). For a finite set `D` of points of
`U` that are closed in `X` and `Set.range jV = Dᶜ`, `inclusion U D ≫ jU` is a closed immersion
(`isClosedImmersion_inclusion_comp`); `compactPointRestriction` and `compactPointBoundary` give
the sequence through `pointScheme U D` (`exact_extensionCohomologyMap_compactPointRestriction`,
`exact_compactPointRestriction_compactPointBoundary`,
`exact_compactPointBoundary_extensionCohomologyMap`), and its third term vanishes in positive
degree when the residue fields at `D` are separably closed
(`subsingleton_H_inverseImage_inclusion_of_sepClosed`). For `F = ℤ/n` and `D = {x}` this is the
lower row of Milne, loc. cit., Thm 14.7, proof, Step 2, p. 94. The comparison of its third term
with that of the point-removal sequence on `X` is not formalized.

## Roots of unity and curves

[CurveRoots](CurveRoots.lean) uses the Kummer root sheaf `Kummer.Coefficients.mu`. For `0 < n`
invertible on `X`, `rootsMap j n hn hinv r : H^r_c(U, μ_n) → H^r(X, μ_n)` is `Sheaf.H.map` of
`rootsExtensionMap`, the extension by zero of the inverse of `rootsPullbackIso` followed by the
original counit (`rootsMap_eq_comp`). With a finite separably closed complement as above,
`rootsMap_bijective_of_sepClosed` and `rootsAddEquiv` hold for `r ≥ 2`, `rootsMap_zero_injective`
in degree zero, and `subsingleton_H_roots_zero_of_injective` when the ring map of global sections
along the support is injective. For `X : FScheme k` with `Curve.Properties X`:
`rootsMap_bijective_of_curve` for `r ≥ 2` over separably closed `k` (for `r = 2` this is the
isomorphism `H^2_c(U, μ_n) ≅ H^2(X, μ_n)` of SGA 4, Exp. XVIII, (1.1.3.1), and of the proof of
Milne, loc. cit., Prop. 14.5); `subsingleton_H_roots_of_curve` for `r ≥ 3` over separably closed
`k`; and `subsingleton_H_roots_zero_of_curve` for `r = 0`, `D` nonempty, over any field. The last
two take `IsUnit (n : k)`; `isUnit_natCast_globalSections` supplies `hinv` from it.

Not asserted: independence of the compactification, purity or local cohomology at points, the
trace `H^2(X, μ_n) ≅ ℤ/n`, and duality.

[RootsComposition](RootsComposition.lean) proves the original coefficient
extension and whole cohomology roots-extension squares in every degree, using
the composed counit and compatible roots isomorphisms. The map equations need
no curve or finite-complement hypothesis.
