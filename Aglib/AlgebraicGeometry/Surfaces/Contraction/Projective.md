# The regular original projective image

`CartierProjectivePresentation.regularStalks_image` proves regularity of every
actual stalk of the original schematic image when the original source has
regular stalks. The exceptional image point is handled by the original
first-order coordinates and the proved local structure-map comparison. On
the actual complementary open, the original isomorphism transfers source
regularity. `image_isIntegral` separately proves integrality of this same
image when the source is integral.

`imageLineBundle` is the pullback of the original `O(1)` along the image's
actual closed projective embedding. `imageLineBundlePullbackIso` identifies
its pullback by the original map with the original corrected coefficient
`H^n(ndE)`. The comparison uses the literal projective-map triangle and the
original section-system isomorphism. This retains the line data needed by
later gluing and ampleness arguments.

`exists_cartier_projective_regular_image` constructs these regular images for
every sufficiently large exponent. It retains the original finite section
presentation, full residue-field closed point, actual complement
isomorphism, exceptional triangle and inverse-image point ideal. Its image
stalk at that point is regular of dimension two. The target is still the
actual closed subscheme of the original projective target.

The input is the original closed projective embedding over a Noetherian
ring, a regular source, the native projective-line Cartier embedding, and
the actual conormal and restricted ample-line comparisons with `O(1)` and
`O(d)`, where `d > 0`. The cohomological construction supplies the required
first-order lifts and sufficiently large exponent. No normality, regularity
or dimension premise is imposed on the constructed image.

`pointIdeal_cartierPullback` transports the proved equality of embedded
ideals to the canonical Cartier predicate. `toImage_isBlowup` then proves
that the original map's canonical lift to the actual point blowup is an
isomorphism, for an integral source. Its literal point fibre is the
original native projective line through the actual Cartier fibre square.
No conormal-coordinate compatibility premise enters the recognition step.
Only the image-point stalk needs regularity, which the original first-order
construction proves; global source regularity is unnecessary for this
identification. Thus a compactification may retain singularities on its
boundary away from the original exceptional curve.

`exists_cartier_projective_pointBlowup` constructs those first-order inputs
and a point-blowup presentation for every sufficiently large exponent,
without global regularity of the integral source. Its
returned presentation retains the actual image line and its corrected
pullback comparison, as well as the full closed point, regular
two-dimensional point stalk, complement and exceptional triangles.

`exists_cartier_projective_contraction` constructs the contraction from the
original geometric inputs. It supplies a regular integral Noetherian target,
the full original field point with a regular two-dimensional stalk, proper
source and structural maps, and an actual closed projective embedding of the
target over the same base. Its canonical blowup isomorphism, inverse-image
ideal, exceptional triangle, structural triangle and complement isomorphism
are retained. The first-order section data are constructed internally.

Extending the contraction beyond this projective setting and proving the
needed relative ampleness and global gluing statements remain subsequent
obligations.
