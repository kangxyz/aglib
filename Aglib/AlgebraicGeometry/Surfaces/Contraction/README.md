# Contraction of exceptional Cartier curves

[The proper contraction theorem](Proper.md), in
`Scheme.Surfaces.Contraction.Proper`, applies to an integral regular
Noetherian scheme X of dimension at most two with a supplied proper map
f:X→S to a Noetherian scheme. The original closed immersion P¹_k→X must
have singleton image in S, a locally rank-one actual kernel ideal, and
actual conormal O(1). Its contraction preserves the full k-point, pulled
Cartier ideal, canonical blowup, complement and original base map.
The target is integral regular Noetherian of dimension two; the maps
retain the stated properness, separatedness and birationality.

[Proper projectivity](../Projectivity.md) constructs the required finite
projective embedding on the actual inverse image of an affine base
neighbourhood. [Proper gluing](ProperGluing.md) then glues this contraction
with the unchanged original complement. An ample bundle or a projective
presentation is not an extra hypothesis of this proper-base endpoint.

The projective construction below supplies the local contraction and its
original ideal, point and coordinate comparisons.

This family, in `Scheme.Surfaces.Contraction`, constructs actual projective
maps and their kernel-ideal images from specified Cartier-line data. The
input is a closed embedding `p : X ⟶ ProjectiveSpace A ι` over a commutative
Noetherian ring, a finite coordinate labeling `ι ≃ Fin (r+1)`, a line bundle
`H` with specified `H ≅ p^* O(1)`, and a closed immersion
`i : E ⟶ X`, where `E = P¹_k` is the native projective line over a
commutative ring `k`. Its actual kernel ideal module `I_E = Hom.idealModule i` is locally rank one. The restriction data
are actual isomorphisms `eI : i^* I_E ≅ O(1)` and
`eH : i^* H ≅ O(d)`, with `d : ℕ`.
The residue-point, complement and point-ideal endpoints further require
`IsField k` and `0 < d`.

[Projective sections](ProjectiveSections.md) constructs the original Cartier
short exact sequences and uses
[Cartier-curve vanishing](../../Cohomology/CartierCurve/Vanishing.md) and
projective Serre vanishing. One bound works for every sufficiently large
`n`: first cohomology of `H^n(jE)` vanishes for `j ≤ nd+1`, and every
original quotient section map before that stage is surjective.
`exists_cartier_finite_section_families` constructs finite sheaf-generating
families through `L_n = H^n(ndE)`; the lower augmentation lemma retains
prescribed extra sections.
These results allow `d = 0`; the later first-order and complement endpoints
use the displayed positivity hypothesis.

[Projective maps and images](ProjectiveImage.md) constructs
`CartierProjectivePresentation` for every sufficiently large `n`. Its
finite family generates `L_n` as a sheaf and spans its actual global
sections over `A`. It retains all mixed coordinates `X_a^(n-1) X_b` under
the original common Cartier multiplier. The native
`ProjectiveSpace.FromSections` map has
the specified twisting pullback and coordinate equations; `image` is its
actual schematic image, and `toImage` is proper and surjective. The
first-order presentation, when `nd ≥ 2`, also retains the two proved lifts of the original
`O_E(1)` coordinates as literal coordinates of this same family.

[The complement comparison](Complement.md) proves
`exists_cartier_projective_complement` under `IsField k` and `0 < d`.
The original residue map `Spec k ⟶ image` is a closed immersion retaining
the full residue field, and the original `toImage` restricts to an actual
scheme isomorphism from `X` minus `E` to its image minus that point. The
base action on `k` is derived from the original structural map; the section
family retains its full span over `A`.

[The image-point ideal](PointIdeal.md) uses those same sections, image,
residue point and first-order coordinates. `pointIdealPullback` is the
original canonical ideal-module map. Its closed pullback is epi by the
actual first-order lifts, and
[closed Nakayama detection](../../Modules/ClosedImmersion/Nakayama.md)
combines finite target stalks with the original off-curve isomorphism.
[Kernel detection](../../IdealSheaf/BaseChange/Detection.md) then gives
`pointIdeal_comap_eq`. The endpoint
`exists_cartier_projective_pointIdeal` retains the same complement
isomorphism and exceptional triangle and proves the literal ideal equality

```lean
(F.pointIdeal eI eH j₀ h₀).comap F.toImage = i.ker
```

The public `pointCartierMultiply`,
`pointCartierMultiply_pullback_isIso` and `pointCartierMultiply_coordinate`
expose the same original multiplier and its pair correspondence for further
formal-neighborhood comparisons, retaining the original selected chart,
coordinate equality and residue-zero equation.

[The local-coordinate construction](FormalNeighborhood/LocalCoordinates.md)
keeps the same presentation, full residue field, selected unit-residue
section `j₀` with witness `h₀`, and surjectivity `hρ` of the original residue
section map. For `2 ≤ n * d`, the two lifts `t` satisfy the original
first-order quotient equations `ht`, and their images occur at the literal
positions `q` of `F.sections` by `hq`. These data define the original image
point `c = F.residueToImage eI eH j₀ h₀`, its stalk `R = pointLocalRing c`,
and the actual local-spectrum source `W = localSource F.toImage (imagePoint c)`.

[The structure-map theorem](FormalNeighborhood/StructureMap.md)
`selectedLocalStructureAndParameters` proves bijectivity of the literal map
`α = localStructureHom F.toImage (imagePoint c) : R →+* Γ(W, ⊤)`.
It also identifies the actual maximal ideal of `R` with the span of the two
selected coordinate germs at `q ⟨0⟩` and `q ⟨1⟩`. Their original degree-one
conormal images form the basis over the full residue field, and
`selectedLocalMaximalIdeal_not_isPrincipal` proves that this maximal ideal
is nonprincipal. The ordinary pushforward-stalk map induced by `toImage.c`
is consequently an isomorphism at this same image point.

[The local-source regularity theorem](Regularity.md) proves regularity and
normality of the actual local source from a regular Cartier closed fibre;
connectedness of that fibre also gives connectedness and integrality of the
local source. Its normality transfer to the target stalk keeps bijectivity
of `α` as an explicit premise. In
[the projective application](Regularity/Projective.md), the structure-map
theorem supplies that premise. The same original image stalk is therefore
a normal domain, and its two generators and nonprincipal maximal ideal give
`ringKrullDim R = 2` and `IsRegularLocalRing R`. A global-section
isomorphism, target normality, or a dimension bound is not an additional
input, and no coefficient-field embedding is chosen.

The actual line comparisons remain inputs. The
[point-blowup criterion](PointBlowup.md) identifies the original proper
modification through its canonical Cartier lift. Its literal closed fibre
is the native projective line, and regularity is needed only at the full
image point. A finite birational comparison on actual stalk pullbacks
allows singularities elsewhere on the target; no openness of the normal
locus or excellence hypothesis is used.

[The projective contraction](Projective.md) constructs a point-blowup
presentation for each sufficiently large exponent when the projective
source is integral. Its actual projective image line pulls back to the
original corrected Cartier power. For a regular source the constructed
target is regular, integral, Noetherian and projective over the same base.
The full point field, pulled ideal, exceptional and structural triangles,
and complement isomorphism are retained.

The proper-base endpoint uses the supplied proper map throughout. A bare
surface without that map is outside its stated scope. The remaining
resolution applications require their own normalization, cohomology and
finite-modification arguments.
