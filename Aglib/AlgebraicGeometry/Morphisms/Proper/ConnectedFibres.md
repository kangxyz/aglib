# Connectedness and actual structural sections

`connectedSpace_of_globalSections_idempotents` proves that a nonempty scheme is
connected when every idempotent of its actual global-section ring is zero or one.
The proof uses the native structural-sheaf product decomposition over the two
open pieces of a clopen decomposition and transports the characteristic
idempotent `(1, 0)` through the actual ring isomorphism.

This criterion requires no properness, flatness, normality or Noetherianity.
For proper morphisms over a locally Noetherian target, the actual affine
formal-functions image theorem and flat base change give the geometric fibre
argument described below. The ordinary pushforward-stalk image theorem is a
separate reusable statement and is not needed for this direct affine route.

`eq_zero_or_one_of_idempotent_stalkToFibreSections_image` applies the proved
residue-field factorization to an idempotent already in the actual ordinary
stalk image. Under `IsIso f.c`, that idempotent is zero or one. This does not
place arbitrary fibre idempotents in the image.

`isIso_c_pullback_snd_of_flat_of_isIso_c` proves that flat change of base
preserves the actual structure-sheaf isomorphism when `f` is quasi-compact and
quasi-separated. Its affine-chart theorem uses the native section pushout
comparison and the actual pushout coprojection; an affine basis then gives
the sheaf isomorphism. Properness, normality and Noetherianity are unnecessary
for this transport result. The geometric application uses only flat stalk and
finite etale base maps; the closed residue-field map need not be flat.

For the remaining geometric passage, purely inseparable change of field
preserves connectedness through the actual integral, bijective base-change
projection. A separate algebraic helper places any idempotent of a tensor
product over an algebraic field extension in the image of an idempotent over
a finite intermediate field. These are lower ingredients used in the geometric detection argument.

The converse section criterion is proved using actual basic opens and germs:
on a preconnected scheme every idempotent structural section is zero or one.
For a field point surjective on stalks, the original induced residue-field map
is an isomorphism. The canonical iterated pullback comparison then identifies
base change by that same field point with the literal original residue fibre,
so connectedness transfers along its actual projection. These comparisons do
retain the actual field-point and original residue-field maps.

The finite-separable residue lift is also expressed as an actual surjective
ring map from a finite etale algebra to the supplied residue extension. Its
composite with the original base-ring map is exactly the original residue map
followed by that field extension. The surjection comes from the actual
residue tensor comparison and its scalar laws. No Henselian or completeness
condition is introduced.

`eq_zero_or_one_of_idempotent_residueFibre_globalImage` is the direct affine
consumer: when the actual structure-sheaf map is invertible, an idempotent of
the literal residue-quotient fibre with an actual global-function preimage is
zero or one. The actual section restriction factors through residue-field
constants by the original pullback square and Spec section comparison. This
uses no ordinary-stalk or derived-zero comparison and leaves the proper image
witness to be supplied by the actual affine formal-functions theorem.

The direct image-witness argument also works for any actual field-valued
ring map from an affine base, without localness of that base. The structure
map and the actual pullback square give the same field-constant triangle.

For a quasi-compact quasi-separated scheme over a field, the actual global
sections after any field extension are identified as a ring with the scalar
tensor product of the original sections. This uses the native flat section
pushout and the native tensor-product pushout. The resulting equivalence is
characterized on pure tensors by the original field constants and projection
section map; no cohomology or nonflat base-change isomorphism is assumed.

For a nonempty quasi-compact quasi-separated scheme over a field, connectedness
after every finite separable field extension detects geometric connectedness.
The proof descends actual tensor idempotents over the separable closure to
finite intermediate fields, then uses the purely inseparable projection to the
algebraic closure and the existing algebraic-closure detector. These finite
extension tests remain explicit premises of the private detection lemma. The
proper application discharges them using the actual affine image theorem.

`exists_section_restrict_eq_of_isIdempotentElem_fieldFibre` transfers the proved
affine ideal-thickening image theorem through the canonical isomorphism from a
surjective field-valued ring map to the quotient by its actual kernel. Every
actual fibre idempotent therefore has an arbitrary original global-function
preimage. No idempotence of that preimage, Henselian hypothesis, completeness,
or nonflat cohomology base-change isomorphism is asserted.

`geometricallyConnected_of_isProper_of_isIso_c` proves that a proper surjective
morphism over a locally Noetherian target is geometrically connected when its
actual structure-sheaf map is an isomorphism. Localizing at the original target
point is flat. Each finite separable residue extension is realized by an actual
surjective map from a finite etale algebra. Flat transport preserves the sheaf
isomorphism there; the affine image theorem forces its closed field-fibre
idempotents to be zero or one. Canonical pullback comparisons then discharge
the finite separable tests for the literal original fibre.

`geometricallyConnected_of_isProper_birational` applies the actual normal-target
birational functions theorem. Its premises are integral source and target,
locally Noetherian target, properness, dominance, `NormalStalks` of the target,
and invertibility of the original `functionFieldMap`. It introduces no supplied
Stein family, model-existence, contraction or Henselian-comparison assumption.
