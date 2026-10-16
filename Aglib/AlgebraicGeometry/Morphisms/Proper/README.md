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
| Projective geometry | Actual polynomial `Proj`, standard polynomial charts, proper structural map, twists, original cohomology computations and finite-type affine projective-chart immersions | Arbitrary-ring projective-space base change and local projective projection coherence; Segre and twist base change can follow later |
| Coherent support | Native stalk support, affine closed support, affine quotient-ring/killed-by-ideal equivalence, coherent closed/finite pushforward, and quasicoherent pushforward from quasi-compact opens | Global coherent submodule extension, support descent or ideal-power devissage, and the actual Noetherian support induction |
| Noetherian topology | `WellFoundedLT (Closeds X)` and finite irreducible decomposition | Use them with actual coherent modules, without a finite Krull-dimension assumption |
| Derived composition | Aglib `derivedPushforwardPlusCompIso` for arbitrary scheme morphisms, with the original pushforward comparison and both derived units | Combine it with proved acyclicity and the actual higher-direct-image/cohomology interfaces; no supplied Leray/composition family |

## Dependency plan

1. Close the graph-closure interface above, including its exact original maps and an independent public consumer.
2. The actual finite-type affine immersion is now supplied by
   [ProjectiveSpace.AffineImmersion](../../ProjectiveSpace/AffineImmersion.lean).
   [DenseAffine](../../Properties/Noetherian/README.md) supplies finite dense
   affine covers of every Noetherian scheme, with dense common intersection.
   Its neighborhood theorem only requires finitely many irreducible components.
3. [Chow](Chow/README.md) constructs the finite native product of
   these original graph closures, its closed pairing into `X` times the target
   product, and its proper surjective source projection. Its original
   restriction to the common open is an isomorphism. The original target map
   is locally an immersion, hence locally quasi-finite; properness and native
   Zariski's Main Theorem make it finite. `Chow.Basic` now supplies all these
   data unconditionally for every proper morphism over a Noetherian affine
   base. No integral or reduced source assumption is needed, and
   scheme-theoretic dominance is not claimed.
4. Prove scheme-level polynomial projective-space base change, then identify
   actual higher images of each projective projection on affine target opens.
   Absolute projective finiteness and its cohomological bound, shared derived
   locality and finite Postnikov give bounded coherent direct images along
   finite projection towers and closed/finite composites. This first route
   does not require Segre, twist pullback or simultaneous relative Serre
   vanishing.
5. For a fixed proper source, use Noetherian induction on a closed set `Z`,
   quantifying over every closed scheme `W → X` with image contained in `Z`
   and every coherent coefficient on `W`. For its graph modification `pi`,
   take the native cone of the ordinary pullback unit followed by the actual
   right-derived pushforward unit. Its bounded coherent homology is supported
   on the strict closed boundary. Actual ideal-power annihilation and
   ideal-killed descent let the induction apply to those finitely many layers;
   the shared finite-Postnikov theorem supplies cone finiteness. This handles
   boundary nilpotents without a global annihilator construction or prime
   filtration.
6. The original derived composition and cone triangle then prove finiteness of
   the unchanged `Sheaf.H` over `Spec R`, with its original structural action.
   Shared actual higher-image localization extends this to proper coherent
   direct images over locally Noetherian bases. These cohomological steps
   remain explicit obligations; no proper-finiteness family is assumed.

The geometric and cohomological route is guided by [Stacks, Chow's lemma](https://stacks.math.columbia.edu/tag/02O2) and [Stacks, proper coherent direct images](https://stacks.math.columbia.edu/tag/02O3). These are mathematical references, not formal premises. Existing projective results remain independently proved; the new geometric and support constructions must discharge every transition to general proper morphisms.

GraphClosure, including both exact open-comparison maps and the literal closed image inclusion, passed the guarded single-leaf build `1792107279295289000-10327` (4.7 seconds).

The independent graph-closure public consumer passed `1792107508980791000-13403`. It checks arbitrary universes, the original maps, dense-open surjectivity without quasi-compactness, and that a locally Noetherian source supplies the exact quasi-compact-open-immersion hypothesis. All inspected declarations use only `propext`, `Classical.choice` and `Quot.sound`.
