# Actual ideal modules and canonical comparisons

[Modules](Modules.lean), imported as `Aglib.AlgebraicGeometry.IdealSheaf.Modules`, defines `Scheme.Hom.idealModule i` as the actual kernel of the structure-module map `𝒪_X → i_*𝒪_D`. Its inclusion and sectionwise kernel equivalences retain the actual ring-section maps. This construction applies to arbitrary scheme morphisms; closed immersion is an additional premise on the results that need it.

[QuotientModule](QuotientModule.lean) defines the structure module `quotientModule W = cokernel (idealInclusion W.subschemeι)` of a closed subscheme with its projection `toQuotientModule`, the short exact sequence `shortComplex_shortExact`, `quotientModuleIsoPushforward : 𝒪_X / I_W ≅ i_* 𝒪_W`, quasi-coherence, and coherence on locally Noetherian schemes (`affineLocallyFiniteType_quotientModule`, `Scheme.Hom.affineLocallyFiniteType_idealModule`). [Order](Order.lean) proves `le_of_idealInclusion_factor`: closed subschemes are ordered by factorization of their ideal inclusions. [Comap](Comap.lean) proves that Mathlib's `subschemeMap (I.comap b) I b (I.le_map_comap b)` forms a cartesian square (`isPullback_subschemeMap_comap`).

[QuotientModule/Map](QuotientModule/Map.lean) proves `quotientModulePushforwardIso : j_* 𝒪_V ≅
𝒪_{V.map j}` for a closed subscheme `V ⊆ X` closed in `Y` (`IsClosedImmersion (V.subschemeι ≫ j)`),
through `mapSubschemeIso` and the pushforward presentations `quotientModuleIsoPushforward`; it is
the pushforward counterpart of `quotientModulePullbackIso`
([BaseChange/QuotientModule](BaseChange/QuotientModule.lean)). The [fibres of embedded
families](../HilbertScheme/Immersed/Fiber.lean) consume it.

[Monomorphism](Monomorphism.lean) compares closed subschemes along a monomorphism `j : X ⟶ Y`
(for example an immersion). It builds on `ker_comap_of_mono`
([Closed/MonoFactor](Closed/MonoFactor.lean)): for `z : Z ⟶ X` with `z ≫ j` a closed immersion,
`(z ≫ j).ker.comap j = z.ker`. Mathlib's pushforward `I ↦ I.map j` and pullback
`J ↦ J.comap j` are inverse bijections between the closed subschemes of `X` that are closed in `Y`
and the closed subschemes of `Y` that factor through `j` (`mapEquivOfMono`,
`comap_map_of_mono_of_isClosedImmersion`, `map_comap_of_comp_eq`; the last needs no
monomorphism hypothesis). The closedness premise is necessary (the non-quasi-compact example in
[Glue](Glue.lean)); `comap_map_of_isClosedImmersion` ([ClosedExtension](ClosedExtension.lean)) is
the case of a closed immersion `j`, and `comap_map_of_isOpenImmersion`
([OpenExtension](OpenExtension.lean)) the equation for a quasi-compact open immersion.
`mapSubschemeIso` identifies a closed subscheme with its image over `Y`. Along a cartesian square
`j₂ ≫ b = a ≫ j₁`, closedness and factorization are preserved, and for a monomorphism `j₁` the
image commutes with pullback (`map_comap_of_isPullback`); `comap_subschemeι_comp_of_isPullback`
transfers any property stable under base change of `I ⟶ X₁ ⟶ T₁` to the pulled-back square. For a
preimmersion `j` and `q : Y ⟶ T`, a closed subscheme proper over `T` is closed in `Y` when `q` is
separated, and properness over `T` is equivalent to closedness in `Y` when `q` is proper
(`isProper_subschemeι_comp_iff_isClosedImmersion`; for immersions in `Over S` the same argument is
`Scheme.isClosedImmersion_of_immersion_over_proper`). The
[immersed Hilbert functor](../HilbertScheme/Immersed/Functor.lean) consumes these results.

[Affine](Affine.lean) compares spectral ideal modules with sheafification of the actual ring kernel and proves the stated finite-generation consequence of finite presentation. [Restriction](Restriction.lean) compares actual ideal restrictions and their inclusions. The [base-change family](BaseChange/README.md) constructs the canonical ideal pullback map, proves epimorphy for a cartesian square of a closed immersion, and gives the separate quotient-flat isomorphism theorem.

[Colon](Colon.md) defines `IdealSheafData.stalkIdeal` from the original affine
germs and detects ideal-sheaf equality and inclusion on these actual stalk
ideals. On a locally Noetherian scheme, `colon I K` has the ordinary ideal
quotient on every affine open and every actual stalk. Its pullback comparison
requires isomorphisms of the original stalk maps, as for open immersions.

[Artinian](Artinian.md) identifies the ideal stalk on the actual quotient
subscheme with the kernel of its closed-immersion stalk map. Under local
Noetherianity, finite length of every original quotient stalk makes that
quotient scheme locally Artinian; finite support additionally makes it
Artinian. These lower bridges serve the
[point-blowup principalization](../Surfaces/Resolution/README.md) and
[rational-coordinate base-ideal](../RationalMap/BaseIdeal.md) constructions.

[Glue](Glue.lean) glues ideal sheaves along open covers. For a jointly surjective family of open immersions `f i : U i ⟶ X` and ideal sheaves `I i` on the `U i` whose pullbacks to the overlaps `pullback (f i) (f j)` agree, `Scheme.IdealSheafData.glue f I hf hI` is an ideal sheaf on `X` with `(glue f I hf hI).comap (f i) = I i` (`comap_glue`). Its ideal on an affine open `V` is `glueIdeal f I V`, the sections whose restrictions to all affine opens of the `U i` over `V` lie in the `I i`; the basic-open condition uses a finite subcover of `V` and the localization of sections at basic opens. Mathlib's pushforward `IdealSheafData.map` does not give this gluing directly, because `(I.map j).comap j = I` can fail for an open immersion `j` that is not quasi-compact (example in the module docstring, checked by hand, not formalized). The Zariski sheaf property of closed subschemes in [Descent/IdealSheaf/Fppf](../Descent/IdealSheaf/Fppf.lean) uses this construction.

[GlueImmersion](GlueImmersion.lean) glues immersions that represent a Zariski-local condition. For a locally Noetherian `X` and a condition `P` on morphisms from locally Noetherian schemes, stable under restriction to opens and local on the source, suppose every point of `X` has an open neighbourhood `U` and an immersion `m : Z ⟶ X` with image in `U` such that a morphism with image in `U` satisfies `P` exactly when it factors through `m`. Then one immersion represents `P` (`Scheme.exists_isImmersion_forall_exists_lift_iff`). Each local immersion is closed in `coborder (range m) ∩ U` (`glueImmersionLift`); the kernels of these closed immersions agree on the overlaps (`comap_ker_glueImmersionLift_eq`), because two closed subschemes of an overlap that represent `P` factor through each other; they glue by `IdealSheafData.glue`. `Scheme.exists_lift_iff_comap_ker_eq_bot` is the factorization criterion through a closed immersion used throughout. The [flattening stratification](../FlatteningStratification/README.md) over a locally Noetherian base consumes it.

[Descent](../Descent/IdealSheaf/README.md) proves faithfully flat descent of closed subschemes (Nitsure, Lemma 6.7(2)) along flat, surjective, quasi-compact morphisms.

[Invertible/Affine](Invertible/Affine.lean) relates actual local ideal bases to regular principal generators. [Effective Cartier consequences](../EffectiveCartierDivisor/README.md) use local rank one of these actual ideals with their stated closed-immersion and smoothness hypotheses. No replacement ideal-sheaf predicate is introduced.

[LocallyClosed](LocallyClosed.lean) describes pulled-back ideal sheaves on affine opens: for `g : Y ⟶ X` and affine opens `V ≤ g ⁻¹ᵁ U`, `(I.comap g).ideal V` is generated by the image of `I.ideal U` under `g.appLE U V` (`ideal_comap_eq_map_appLE`, Stacks Project, Tag 01JU; `comap_eq_bot_iff_forall`, `comap_eq_top_iff_forall`), and a point `fromSpec p` of an affine open `V` lies in the support of `I` if and only if `I.ideal V ⊆ p` (`fromSpec_mem_support_iff`). A morphism factors through `I.subschemeι` if and only if `I.comap g = ⊥` (`exists_lift_subschemeι_iff`) and lands in the complement of the support of `J` if and only if `J.comap g = ⊤`. `locallyClosedι I J` is the immersion of the open subscheme of `V(I)` complementary to `V(J)`; its image is `supp I \ supp J` (`range_locallyClosedι`) and `exists_lift_locallyClosedι_iff` is its universal property. The [Fitting strata](../FlatteningStratification/README.md) consume these results.

For pullbacks of combinations of ideal sheaves, the same leaf proves
`Scheme.IdealSheafData.comap_iSup_eq_bot_iff` (a supremum over any index type
pulls back to zero iff every member does), `comap_mul_eq_top_iff` and
`comap_finset_prod_eq_top_iff` (a finite product pulls back to the unit ideal
sheaf iff every factor does), and `notMem_support_finset_prod_iff` (a point lies
outside the support of a finite product iff it lies outside the support of
every factor). The refined joint rank strata of the flattening stratification
consume them.

[Cartier interfaces](Cartier/README.md) and
[closed-subscheme constructions](Closed/README.md) organize the incoming
ideal-sheaf comparisons. [ReducedClosedUnion](Closed/ReducedClosedUnion.lean),
[IntersectionComparison](Closed/IntersectionComparison.lean) and
[SpecKernel](Closed/SpecKernel.lean) keep the original ideals, maps and reducedness
hypotheses.

[RegularSurface](Invertible/RegularSurface.md) proves local rank one of the
same actual `idealModule i` for a closed immersion `i : C ⟶ X` with integral
`C`, locally Noetherian `X`, every ambient stalk regular local of dimension at
most two, and every actual kernel `RingHom.ker (i.stalkMap c).hom` of height
one. The explicit height and local Noetherianity conditions remain part of
the theorem. The shared [stalk-kernel criterion](Invertible/StalkKernel.md)
uses actual singleton kernel bases, and [Factorial](Invertible/Factorial.md)
supplies them in arbitrary dimension under explicit factorial-domain
structures on the actual stalks. [Cartier operations](Cartier/README.md)
provide avoidance, ideal tensor-product and DVR-fibre comparisons.

[Regular-stalk Cartierness](Cartier/Regular.md) supplies these factorial
structures from regularity of every actual ambient stalk, using the general
regular-local UFD theorem. Its actual closed immersion, integral source,
locally Noetherian ambient scheme and height-one stalk-kernel conditions
remain explicit, with no dimension bound.

[Noetherian](Noetherian.lean) gives `WellFoundedGT X.IdealSheafData` for a
Noetherian scheme. A finite affine cover reduces ascending chains of the
actual quasi-coherent ideals to ring-ideal stabilization with one common
index. The induction retains nilpotent structure; strict closed subschemes
produce strict increases of the original ideal, not merely changes of closed
support. [Proper Grothendieck existence](../Cohomology/GrothendieckExistence/Proper.md)
uses this induction on its actual closed-subscheme thickenings.

## Finite-type ideals and closed approximation

[FiniteType](FiniteType.lean), imported as
`Aglib.AlgebraicGeometry.IdealSheaf.FiniteType`, defines
`Scheme.IdealSheafData.AffineLocallyFG`: the actual ideal on every affine open
is finitely generated. `affineLocallyFG_iff_affineLocallyFiniteType` identifies
it with finite type of the native ideal module. The lower
`Scheme.Hom.idealModule_isQuasicoherent` needs only an affine morphism.
For a closed immersion `e`, [FinitePresentation](FinitePresentation.lean)
proves `Scheme.Hom.locallyOfFinitePresentation_iff_ker_affineLocallyFG`.
No Noetherian hypothesis occurs in these criteria.

[FiniteTypeExtension](FiniteTypeExtension.lean), imported as
`Aglib.AlgebraicGeometry.IdealSheaf.FiniteTypeExtension`, proves
`IdealSheafData.exists_affineLocallyFG_extension_le`. On qcqs `X`, for a
compact open `U`, an ambient ideal `I` and an affine-locally finitely generated
`K ≤ I.comap U.ι`, it returns `J ≤ I` with `J.AffineLocallyFG` and the literal
equality `J.comap U.ι = K`.

[FiniteTypeApproximation](FiniteTypeApproximation.lean), imported as
`Aglib.AlgebraicGeometry.IdealSheaf.FiniteTypeApproximation`, defines
`FiniteTypeSubideal I := {J // J ≤ I ∧ J.AffineLocallyFG}` in the original
scheme universe. This is a nonempty filtered category.
`iSup_finiteTypeSubideal` proves `(⨆ J : FiniteTypeSubideal I, J.val) = I` on a
qcqs scheme. These are actual subideals and inclusions.

[FinitePresentationApproximation](FinitePresentationApproximation.lean),
imported as `Aglib.AlgebraicGeometry.IdealSheaf.FinitePresentationApproximation`,
takes the opposite index to produce finitely presented closed subschemes
over `X`. `finitePresentationApproximationConeIsLimit` and its scheme-valued
form prove that their limit is the closed subscheme defined by `I`, for qcqs
`X`. Transitions are closed immersions. No nilpotence or equality of stage
supports is asserted.

For an arbitrary category-indexed ideal diagram, [Limits](Limits.lean) gives
`IdealSheafData.subschemeSupConeIsLimit` in `Over X` without a connectedness
hypothesis. Its forgotten scheme limit
`subschemeSupSchemeConeIsLimit` requires `[IsConnected C]`. The cofiltered
finite-subideal approximation satisfies this requirement. The
[closed-immersion interface](../Morphisms/ClosedImmersion/README.md) returns
the original source and structural triangles; the
[approximation family](../Approximation/README.md) consumes these lower
constructions.

[EmptySubscheme](EmptySubscheme.lean) characterizes the empty closed subscheme of an arbitrary
scheme: `Scheme.IdealSheafData.isEmpty_subscheme_iff` (`W` has no point iff `W = ⊤`),
`nonempty_subscheme_iff`, and `isZero_quotientModule_iff` (`𝒪_X / I_W = 0` iff `W = ⊤`). The last
goes through `quotientModuleIsoPushforward`: modules on an empty scheme vanish
(`Scheme.Modules.isZero_iff_stalks`), and the global sections of `i_* 𝒪_W` form the ring
`Γ(W, ⊤)`, nontrivial when `W` has a point. The nonvanishing of Hilbert polynomials of nonempty
subschemes ([HilbertScheme/Nonempty](../HilbertScheme/Nonempty.lean)) consumes it.

[GlueDisjoint](GlueDisjoint.lean) glues ideal sheaves along a jointly surjective family of open
immersions with pairwise disjoint images, with no compatibility hypothesis:
`Scheme.IdealSheafData.glueOfDisjoint`, `comap_glueOfDisjoint`, `eq_glueOfDisjoint_iff`. The
overlap condition of [Glue](Glue.lean) holds automatically
(`comap_fst_eq_comap_snd_of_pairwise_disjoint`; ideal sheaves on an empty scheme agree,
`eq_of_isEmpty`). Any index universe.

[GlueCoproduct](GlueCoproduct.lean) glues closed subschemes `D j ⊆ Z ×_S H j` to
`Scheme.IdealSheafData.sigmaGlue πZ πH D ⊆ Z ×_S ∐_j H j` along the components
`Scheme.pullbackSigmaι` ([Limits/CoproductPullback](../Limits/CoproductPullback.lean)):
`comap_sigmaGlue`, `eq_sigmaGlue_iff`, and `comap_sigmaGlue_pullbackMap` (pullback along a map into
one component). `ext_of_comap_pullbackMap_eq`: closed subschemes of `Z ×_S T` agreeing over an
open cover of `T` are equal. Any small index type. Consumers:
[HilbertScheme/Coproduct](../HilbertScheme/Coproduct/Family.lean).

[ImageOverBase](ImageOverBase.lean) compares a closed subscheme `I ⊆ X` that is closed in `Y` along
`j : X ⟶ Y` with its image `I.map j`, over a base `q : Y ⟶ T` with `j ≫ q = p`: they have the same
image in `T` (`Scheme.IdealSheafData.range_map_subschemeι_comp`) and the same properties respecting
isomorphisms (`map_subschemeι_comp_iff`), through `mapSubschemeIso`
([Monomorphism](Monomorphism.lean)). No hypothesis on `j`, `q` or the schemes. Consumer:
[HilbertScheme/Coproduct/Functor](../HilbertScheme/Coproduct/Functor.lean).
