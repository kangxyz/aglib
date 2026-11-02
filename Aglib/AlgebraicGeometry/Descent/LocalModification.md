# Local replacement of a stalk modification

Source: [LocalModification.lean](LocalModification.lean).

Import `Aglib.AlgebraicGeometry.Descent.LocalModification`.
Declarations belong to `AlgebraicGeometry.Scheme.LocalModification`.

## Generic construction from an actual punctured isomorphism

`exists_stalkReplacement` assumes only a locally Noetherian scheme `X`, a
closed point `x`, a proper original morphism
`p : T ⟶ Spec (X.presheaf.stalk x)`, and the actual isomorphism of its
restriction over the inverse image of `X \ {x}`. It constructs
`StalkReplacement x hx p`: a proper global morphism, an isomorphism off `x`,
and a cartesian square retaining that original `p`. In particular it makes
no normality, dimension, integrality or absolute separatedness assumption.
The stronger surface wrapper below derives the punctured-isomorphism input.

`regularStalks_of_local_replacement` derives regularity of the replacement
from regularity of the supplied local scheme and of the unchanged complement.
Its proof transports the actual local rings in the constructed cartesian
square, not regularity along an arbitrary flat base change.

## Normal integral surface wrapper

Let `X` be a normal integral Noetherian scheme with
`topologicalKrullDim X ≤ 2`, and let `x` be a closed point different from
`genericPoint X`. Let

    p : T ⟶ Spec (X.presheaf.stalk x)

be the original proper dominant morphism supplied by the caller. Assume
that `T` is integral with `NormalStalks T` and that the actual
`Scheme.functionFieldMap p` is an isomorphism.

`exists_localReplacement` constructs `LocalReplacement x hx p`. Its fields
supply an integral normal scheme `Y`, a proper dominant morphism `h : Y ⟶ X`,
and an actual morphism `a : T ⟶ Y`, with

    IsPullback a p h (X.fromSpecStalk x),
    IsIso (h ∣_ pointComplement x hx),
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h)).

The final field uses the constructed integral and dominance instances.
The output record is constructed by the theorem; it is never a premise of
that theorem. There is no excellence, finite-normalization, projectivity,
complete-base, rationality or resolution assumption.

The input dimension bound concerns the original `X`. The point must be
closed so that its complement is open, and nongeneric so that this open
contains the generic point. The construction covers local rings of
dimension one as well as two.

The original stalk spectrum is a limit of affine neighbourhoods. The
indexing category consists of actual affine opens containing `x`, ordered
by inclusion. Its inclusion in all open neighbourhoods is initial. The
original section rings and restriction homomorphisms therefore have the
original stalk as their colimit. Applying `Spec` gives the limiting cone,
with projection `Spec.map (X.presheaf.germ W x hxW)` and the equation

    projection ≫ IsAffineOpen.fromSpec = X.fromSpecStalk x.

`exists_proper_affineNeighborhood_model` applies finite-presentation descent
to the actual `p` and then eventual properness. It retains `T` and `p` in
the cartesian comparison at each rebase. It makes no normality or
integrality assertion about the intermediate stage model.

The canonical map from the local spectrum is a flat preimmersion with
image the generizations of `x`. Its actual stalk maps are isomorphisms.
Thus its source is normal and integral, is Noetherian, and has dimension
at most that of `X`. The proper birational isomorphism-locus theorem puts
every nonclosed point of that local spectrum in the target isomorphism
locus of `p`. The unique possible omitted point is its closed point.
`isIso_restrict_punctured_stalkSpec` gives the actual punctured restriction
isomorphism.

Write `U = X \ {x}`. Restrict every affine neighbourhood to its preimage of
`U`. These stages are quasi-compact and quasi-separated, and their transition
maps are affine. Their limit is the original preimage of `U` in the local
spectrum. The stages need not be affine. The restricted original model
square and eventual isomorphy yield
`exists_proper_affineNeighborhood_model_isIso`: an actual proper stage
model whose whole overlap with `U` is an isomorphism.

`glueNeighborhood` glues that model to `U` using the original restricted
structural isomorphism. It constructs the binary open-span colimit and the
map to `X`. The chart preimages equal the actual chart ranges, giving both
cartesian chart squares. Properness follows locally on the target from the
proper neighbourhood model and the identity on `U`. The map from `T` to
the glued scheme is the original model map followed by its chart inclusion.
Pasting the two actual squares gives the required original pullback square.

For a resulting square `H`, the alternative local comparison is

    H.isoPullback.symm : pullback h (X.fromSpecStalk x) ≅ T.

Its map to the original local base satisfies
`H.isoPullback.inv ≫ p = pullback.snd h (X.fromSpecStalk x)`.
No unrelated isomorphism of local models or function fields is substituted.

Every point of `Y` above `x` lifts to `T`, and the original projection induces
an isomorphism on its local rings. `originalStalkArrowIso` compares the actual
arrows `h.stalkMap (a t)` and `p.stalkMap t`, preserving their structural and
induced residue maps. Normality above `x` follows from normality of `T`;
normality off `x` follows from the restriction isomorphism to `U`.

The image of the generic point of `T` maps to the generic point of `X` and
is generic on the integral open over `U`. It specializes to every point
above `x`, by lifting that point to `T`. Hence it is dense in the whole of
`Y`, excluding additional components supported above `x`. Normal stalks
imply reducedness, so `Y` is integral. The inverse over `U` proves dominance
of `h`. Finally, functoriality of the original generic-point stalk maps on
the common open proves that `Scheme.functionFieldMap h` is an isomorphism.

The finite-presentation replacement is
[Stacks Lemma 32.21.1, tag 0B3X](https://stacks.math.columbia.edu/tag/0B3X),
and preservation of properness is
[Stacks Lemma 32.21.2, tag 0BFN](https://stacks.math.columbia.edu/tag/0BFN).
The affine and punctured neighbourhood limit/gluing proof is
[Stacks Lemma 32.20.1, tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA).
Normality and integrality of the constructed scheme are derived separately
as above; preservation of an integral morphism is not used to infer that
the source scheme is integral.

The current consumer is the passage from global vanishing of the original
first higher direct image on a normal surface model to arbitrary normal
proper birational modifications of its closed-point local rings. The
comparison between local `H¹` and the stalk of that higher direct image
belongs to the separate flat-localization argument.

## Prescribed normalized-point chains

[SupportedChain](LocalModification/SupportedChain.md) constructs a native
global chain from a supplied proper local normalized-point chain and its
actual punctured comparison. [SurfaceChain](LocalModification/SurfaceChain.md)
derives that punctured comparison on an integral normal Noetherian surface.
The output retains the original terminal Cartesian square, exact chain
length and unchanged complement. The local resolving chain is supplied;
the replacement construction does not prove its existence.

Finite-family serialization and unconditional resolution are separate
mathematical requirements and are not asserted by this module.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalImageFrame](../Cohomology/Duality/Projective/Relative/NormalSurface/LocalImageFrame.md), [AlgebraicGeometry/Descent/LocalModification/Dimension](LocalModification/Dimension.md), [AlgebraicGeometry/Descent/LocalModification/FactorReplacement](LocalModification/FactorReplacement.md).
