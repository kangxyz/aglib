# Proper graph closures and the proper-finiteness route

This family supplies geometric prerequisites for proper Noetherian coherent-cohomology finiteness. It uses the existing scheme objects and original morphisms. The general proper finiteness theorem and Chow's lemma are separate goals; neither is assumed as a theorem-family input.

[GraphClosure](GraphClosure.lean) takes `f : X → S`, `g : Y → S`, an open `U` of `X`, and an actual `S`-morphism `h : U.toScheme → Y`. Its scheme is exactly the native `Hom.image` of `pullback.lift U.ι h w`; its two projections are the native `imageι` followed by the native fiber-product projections. Pairing these projections recovers `imageι` itself.

If `g` is proper, the original projection `p` to `X` is proper. With the precise additional assumption `[QuasiCompact U.ι]`, `toSourceRestrictIso` identifies the original inverse image of `U` with `U.toScheme`: its forward map is exactly `p ∣_ U`, and its inverse is the original open-immersion lift of `Hom.toImage`. The proof uses the native open dense image of a quasi-compact immersion. Its lift over `U` is a proper open dense section, hence an isomorphism. If `U` is dense, `p` is surjective; this last result does not need quasi-compactness of `U.ι`. Properness of `f` also makes the other projection proper. No Noetherianity, reducedness, field or separated-source hypothesis is imposed on this construction.

## Source audit

The audit is against the task's pinned Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612` and the current local Aglib sources.

| Ingredient | Existing interface | Remaining work |
| --- | --- | --- |
| Closed subschemes and images | Mathlib `Scheme.IdealSheafData.subscheme`, `Hom.image`, `imageι`, `toImage`; ideals, radicals and `vanishingIdeal` | Assemble these native objects into the Chow modification |
| Quasi-compact immersions | Mathlib `IsImmersion.isPullback_toImage_liftCoborder` and the open-immersion instance on `toImage` | The original graph-closure projections are supplied here |
| Proper quasi-finite maps | Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite` in `ZariskisMainTheorem` | Apply it to the constructed morphism; no new finiteness criterion is needed |
| Projective geometry | Actual polynomial `Proj`, standard polynomial charts, proper structural map, twists and original cohomology computations | Finite-type affine projective-chart embeddings, projective products/Segre, and the arbitrary-ring projective-space base-change/twist comparison |
| Coherent support | Native stalk support, affine closed support, affine quotient-ring/killed-by-ideal equivalence, coherent closed/finite pushforward, and quasicoherent pushforward from quasi-compact opens | Global coherent submodule extension, support descent or ideal-power devissage, and the actual Noetherian support induction |
| Noetherian topology | `WellFoundedLT (Closeds X)` and finite irreducible decomposition | Use them with actual coherent modules, without a finite Krull-dimension assumption |
| Derived composition | Aglib `derivedPushforwardPlusCompIso` for arbitrary scheme morphisms, with the original pushforward comparison and both derived units | Combine it with proved acyclicity and the actual higher-direct-image/cohomology interfaces; no supplied Leray/composition family |

## Dependency plan

1. Close the graph-closure interface above, including its exact original maps and an independent public consumer.
2. Embed an arbitrary finite-type affine `R`-scheme into a standard chart of finite polynomial projective space, retaining its original structural map. Construct the needed native finite projective products. Defer Segre if iterated projective projections close the cohomological argument with fewer new geometric interfaces.
3. For an integral proper source, form the finite fiber product over the source of the individual graph closures of a finite nonempty affine cover. The original projections should be proper surjective and isomorphisms on the dense common open. On the inverse image of each cover member, use its projective immersion to prove local quasi-finiteness of the map to the product of projective spaces. Properness and native Zariski's Main Theorem then give a finite map to the product. Actual finite pushforward followed by proved successive projective direct-image calculations can suffice for the cohomological reduction; an optional Segre comparison gives a finite map to one projective space. These construction and local quasi-finiteness claims remain to be proved.
4. Establish the projective-space base-change and twist pullback comparisons needed over affine opens of a nonaffine target. Extend the existing absolute projective finiteness and Serre vanishing through actual closed or finite pushforward. For the product route, choose the exponents one factor at a time, simultaneously for the projection chain over the source and the chain over the affine base. Prove coherence and higher-direct-image vanishing at each stage and use native derived composition; no product finiteness premise is supplied.
5. Prove global coherent support devissage. Quasicoherent open pushforward and kernels can extend local submodule graphs; the existing affine annihilated-module equivalence supplies the closed-support algebra. Noetherian induction on closed supports handles all coherent coefficients, including nonreduced and reducible sources, while only requiring Chow on integral closed subschemes.
6. Use the original bounded-below derived composition and the constructed acyclic coefficient to complete proper coherent direct-image finiteness. Over `Spec R`, retain the existing structural-ring action and identify the result with finiteness of the unchanged `Sheaf.H`.

The geometric and cohomological route is guided by [Stacks, Chow's lemma](https://stacks.math.columbia.edu/tag/02O2) and [Stacks, proper coherent direct images](https://stacks.math.columbia.edu/tag/02O3). These are mathematical references, not formal premises. Existing projective results remain independently proved; the new geometric and support constructions must discharge every transition to general proper morphisms.

GraphClosure, including both exact open-comparison maps and the literal closed image inclusion, passed the guarded single-leaf build `1792107279295289000-10327` (4.7 seconds).

The independent graph-closure public consumer passed `1792107508980791000-13403`. It checks arbitrary universes, the original maps, dense-open surjectivity without quasi-compactness, and that a locally Noetherian source supplies the exact quasi-compact-open-immersion hypothesis. All inspected declarations use only `propext`, `Classical.choice` and `Quot.sound`.
