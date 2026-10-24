# Actual square-zero line-bundle lifting

The principal namespace is `AlgebraicGeometry.Scheme.Modules.Invertible`.
All conclusions concern actual module sheaves, original scheme pullbacks
and actual isomorphisms.

| Module | Result and conditions |
| --- | --- |
| [Affine](Affine.lean) | Actual line bundles lift across a surjective square-zero scalar map; a prescribed pullback isomorphism between given affine bundles lifts with equality of its original forward map |
| [AffineMorphism](AffineMorphism.lean) | The same results for an actual morphism between arbitrary affine schemes, through canonical affine-spectrum isomorphisms |
| [ClosedImmersion](ClosedImmersion.lean) | The intrinsic condition `i.ker ^ 2 = bot` gives the original affine ring kernels and is preserved by actual open pullback; closed immersions supply affine section surjectivity |
| [TwoAffine](TwoAffine.lean) | Every actual line bundle lifts across a square-zero closed immersion when its target has the specified two-affine cover with affine categorical intersection |
| [KernelOpens](KernelOpens.lean) | `ker_app_sq_eq_bot`: for quasi-compact `i` with `i.ker ^ 2 = ⊥`, the ring kernel of `i.app V` is square-zero on every open `V`, from the affine case and affine-local vanishing of sections; consumer `Picard/Tangent/Thickening` |

The two-affine theorem uses the actual local projective-module lifts and
the specified overlap-isomorphism lift. Native binary descent glues them,
and full faithfulness of original open-cover descent identifies the
original closed-fibre pullback with the specified input bundle. No
Noetherian, reducedness, ring-splitting or base-flatness hypothesis is used.

The [lower ring Picard theorem](../../../../RingTheory/PicardGroup/README.md)
proves affine Picard invariance. The two-affine theorem gives global
lifting; it does not assert global Picard injectivity. Compatible formal
systems and proper algebraization have the separate `Formal/` owner.
