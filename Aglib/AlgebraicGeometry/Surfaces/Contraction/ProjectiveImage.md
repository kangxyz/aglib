# Actual projective maps and images from Cartier sections

`ProjectiveImage.lean` consumes the fixed Cartier vanishing and finite-family
results from `ProjectiveSections.lean`. The input remains an actual closed
projective embedding with finite coordinate labeling `ι ≃ Fin (r+1)`, an actual
very ample coefficient, the original invertible Cartier ideal, and its native
projective-line restriction comparisons.

`exists_cartier_projective_presentation` constructs a finite original family
that both generates the coefficient `L_n = H^n(ndE)` as a sheaf and spans all its
actual global sections over the original base ring. It retains every original
mixed section `X_a^(n-1) X_b`, pulled back along the original embedding and
multiplied by the original common Cartier inclusion. These maps occupy literal
coordinates through `mixedIndex`.

The returned presentation contains the constructed family and its proved
properties. Its projective morphism is defined by the native FromSections
constructor. `twistingPullbackIso` identifies the actual pullback of `O(1)` with
`L_n`; `coordinateMap_comp` preserves every original section map, including all
mixed coordinates. The scheme-theoretic image is the native kernel-ideal image
of that actual morphism. The original image and structural triangles are
retained, and the map onto the image is proper and surjective.

`sectionFamilySpans_after_surjective` retains the full base-ring span after an
original surjective quotient section map. `exceptionalBaseHom` uses the actual
projective global-functions ring equivalence to define the original base action
on k. Its triangle factors the original structural map to `Spec A` through the
original `P1_k -> Spec k`; factoring the projective map is a separate comparison.
Selecting only the section 1 would not suffice for a nonrational residue
extension.

`firstOrderQuotientIso` identifies the original quotient of `L_n(-E)` by
`L_n(-2E)` with the actual direct image of `O_E(1)` when `nd>=2`.
`exists_firstOrder_coordinate_lifts` lifts both original coordinate sections
through that actual quotient map, using the proved vanishing theorem. Retaining
their subsequent Cartier images as literal projective coordinates is performed
by `exists_cartier_firstOrder_projective_presentation` below. The actual
scheme-theoretic exceptional fibre still requires the point-ideal comparison.

`cartierStepSequence_g_eq_unit` identifies the actual quotient arrow with the
original pullback/pushforward adjunction unit, using the original projection
formula and tensor-section comparisons. `cartierFinalRestrictionIso` constructs
`L_n|E ≅ O_E` from the given comparisons. `cartierResidueMap` is that actual
restriction followed by its displayed trivialization, and
`exists_cartierResidueMap_sections_surjective` proves it is onto all original
residue sections for large n with `nd>=1`. Thus the global generator images use
the genuine restriction map; no abstract isomorphic quotient map is substituted.
The identity `m_z O_X = I_E`, actual ideal powers, associated graded ring and
target regularity require their further actual comparisons. No regularity or
mixed-characteristic coefficient-field assertion is included in this stage.

The section-family construction allows d=0, as does its fixed provider. Choosing
n with `nd>=2` for the uniform first-order and complement stage uses the
originally supplied d>0 in `Complement.lean`.
The global-functions comparison is valid over arbitrary commutative k; residue
point and regular-dimension-two conclusions belong to the actual field case.

`exceptionalGlobalSectionsLinearEquiv` identifies the actual pushed structure
sections linearly with k for the original A-action. `cartierResidueCoefficient`
uses each literal pulled section and the actual final trivialization.
`residueCoefficients_span` proves that these same original coefficients span
all k over A when the proved original restriction is onto. In particular, over
a field, a usable unit coefficient occurs among the original projective coordinates.

`residuePoint` is the native map from the actual `Spec k`, using the same index
and the literal coefficient section maps. `exceptional_toProjective_eq` proves
that the original projective restriction to E is the composite of its original
`P1_k -> Spec k` with this map, preserving every original coordinate.
`exists_cartier_projective_residue_factor` constructs the family and this factor
for all sufficiently large n from the original inputs, with the explicit field
condition on k and original d>0. No section-lift, generation or factorization
oracle is added. Its factor through the original image is constructed below.
The closed point and complement inverse are supplied by `Complement.lean`;
the actual exceptional ideal identity remains a further obligation.

`residueToImage` is the actual Spec k morphism into the original kernel image,
with both original triangles. Its construction uses schematic dominance of the
original `P1_k -> Spec k` and actual image-kernel containment. The original full
coefficient span makes k finite over its original base action, hence this point
map and its image factor are proper. `Complement.lean` applies the genuine
field-span chart-ring theorem to prove this same original point map a closed
immersion, retaining its entire residue field.

`append` retains both old and prescribed new literal coordinates.
`exists_cartier_firstOrder_projective_presentation` applies it to the actual
lifted pair of original O_E(1) coordinates, mapped into L_n by the next original
Cartier inclusion. Their original quotient equations and exact projective
coordinate positions are retained, and their actual restriction to E is zero.

The common Cartier inclusion is an isomorphism on the original open complement
of E, proved from its actual short exact sequences and off-image stalk
vanishing. It restricts to zero on E for nd>=1. The original mixed homogeneous
fraction on the a chart is the original ratio X_b/X_a. These are native inputs
for the actual local and global complement inverse in `Complement.lean`.
The point-ideal identity and regularity of the target remain separate results.
