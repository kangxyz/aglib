# Projective images of an exceptional Cartier curve

This family, in `Scheme.Surfaces.Contraction`, constructs actual projective
maps and their kernel-ideal images from specified Cartier-line data. The
input is a closed embedding `p : X ⟶ ProjectiveSpace A ι` over a commutative
Noetherian ring, a finite coordinate labeling `ι ≃ Fin (r+1)`, a line bundle
`H` with specified `H ≅ p^* O(1)`, and a closed immersion
`i : E ⟶ X`, where `E = P¹_k` is the native projective line over a
commutative ring `k`. Its actual kernel ideal module `I_E = Hom.idealModule i` is locally rank one. The restriction data
are actual isomorphisms `i^* I_E ≅ O(1)` and `i^* H ≅ O(d)`, with `d : ℕ`.
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

The actual line comparisons remain inputs. The
[local regular-point normal-line theorem](../../Blowup/RegularPoint/Normal.md)
has its own native regular-local dimension-two scope. Normality or
regularity of the image point, invertibility of the original structure-sheaf
map `toImage.c`, formal-functions comparisons and a general contraction or
factorization theorem remain further obligations. No coefficient-field
embedding into an ambient local ring is supplied or assumed.
