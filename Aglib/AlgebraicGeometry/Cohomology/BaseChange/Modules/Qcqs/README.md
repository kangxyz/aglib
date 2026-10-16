# Canonical flat base change on qcqs schemes

[MayerVietoris](MayerVietoris.lean) constructs
`moduleMayerVietorisTensorSequenceMap` from scalar extension of the original
six-term module Mayer–Vietoris sequence to the original sequence on actual
inverse-image opens. Its components are the original `moduleHPrimeTensorMap`
and the native binary-biproduct comparison. The restriction sum, restriction
difference and native connecting homomorphism commute with these actual
forward maps. The connecting-map proof uses the original scalar adjunction
unit and faithful scalar forgetting to the native geometric Ext identity.

These constructions work for arbitrary coefficient arrows and compatible
structural ring maps. They impose no flatness, quasicoherence, separation or
covering hypothesis. Flat scalar extension is used in the gluing step below.

[Gluing](Gluing.lean) proves that flat scalar extension preserves this
actual native exact sequence. `moduleHPrimeTensorMap_isIso_sup` uses the
native five lemma to glue invertibility in every degree from the two opens
and their intersection. Its zero-degree proof uses the original monomorphic
restriction map from [Scalars/Zero](../../../MayerVietoris/Scalars/Zero.lean).
The gluing theorem takes the local invertibility statements explicitly;
there is no quasicoherence or separation premise in this step. The final
geometric theorem discharges those local statements using the compact
separated-open comparison below and native finite-affine-union induction.

[Open](Open.lean) proves `moduleHPrimeTensorMap_restrict`, an equality of
the original open tensor mate with the original cohomology tensor mate on
the restricted source. Both sides retain the actual structural scalar
actions, original open equivalences and original cartesian coefficient
isomorphism. The equality needs no quasicoherence or flatness.
`moduleHPrimeTensorMap_isIso_app_of_isSeparated_open` then applies the
supplied-square separated theorem on any compact separated source open,
for a flat ring map and arbitrary quasicoherent coefficients. The ambient
scheme need not be separated.

[Qcqs](../Qcqs.lean) proves
`moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback` on an
arbitrary supplied cartesian square over a flat ring map. Its only geometric
hypotheses are quasi-compactness and quasi-separatedness of the morphism to
an affine base, and quasicoherence of the original coefficient module.
`moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated` specializes it to
the actual fibre product. Both statements use the original tensor mate on
unchanged additive `Sheaf.H`, in every nonnegative degree, with the native
module pullback unit and original structural scalar actions.

The proof uses native compact-open induction. At each finite-affine-union
step, quasi-separatedness makes the overlap compact; as an open of the
added affine, that overlap is separated. The supplied-square separated
theorem therefore applies to the overlap, without a separation hypothesis
on the ambient scheme. The original Mayer–Vietoris maps glue these actual
local tensor maps, and the original whole-space comparison identifies the
result with the canonical global tensor map. No Noetherianity, properness,
finite presentation, finite generation or finiteness of cohomology is used.
