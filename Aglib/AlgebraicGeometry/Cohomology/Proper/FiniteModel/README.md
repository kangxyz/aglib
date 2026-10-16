# One actual finite-projective model for a proper direct image

[FiniteModel](../FiniteModel.lean) uses the sole
[finite-cover model](../../FiniteModel/Basic.lean). There is no new proper
or base-changed model record. Its exact geometric inputs are a
Noetherian commutative ring `R`, an actual proper morphism
`f : X ⟶ Spec R`, a coherent coefficient
`affineLocallyFiniteType X M`, and actual `Modules.relativeFlat f M`.
Flatness of `f` is not required.

`nonempty_finiteCechCohomologyModel_of_proper` constructs that original
model for a supplied finite affine cover and enumeration. The proved
`moduleCohomology_finite_of_proper` discharges actual original cohomology
finiteness internally. No finiteness or comparison family is an endpoint
premise.

`exists_finiteCechCohomologyModel_of_proper` supplies the cover internally.
It uses an actual finite subcover of `X.affineCover`, adds an empty open,
and enumerates it by `ULift.{u} (Fin (n+1))`. The lifted index preserves
arbitrary universe `u`; the empty open includes empty sources and the zero
base ring without a nonempty or nontriviality assumption. The returned
`FiniteCechCohomologyModel` contains the actual bounded finite-projective
complex `P`, its original arrow to the original finite Cech complex, that
arrow's quasi-isomorphism, and the same literal arrow's quasi-isomorphism
after every ring scalar extension. The shared methods compute unchanged
`Sheaf.H.{u+1}` and installed native derived global sections.

`exists_finiteProjective_derivedPushforward_model_of_proper` returns one
native bounded-below module complex `P`, strict term bounds `[0,n]`,
finite-projective terms, and a native strict-perfect representative of
installed `Rf_*(single M)` given by actual tilde of `P`. Within the same
existential, for every commutative new ring `S` and every `R →+* S`, literal
scalar extension of this same `P`, followed by native tilde on `Spec S`,
has the same term bounds, is strict perfect, and represents installed
direct image of the ordinary pulled coefficient on the actual fibre
product. The new ring needs neither Noetherianity nor flatness.

The direct-image object isomorphisms use the original exact-tilde derived
units, actual spectrum-section comparison, proved original tilde/sections
counit and original injective-resolution comparison. No second chain
representative is selected. Equality to a separately chosen chain-normalized
isomorphism is a further normalization obligation. The shared
[BaseChange](../../FiniteModel/BaseChange.lean) independently retains the
full original geometric degreewise map/native homology-mate square.
Computing all base changes does not assert every degreewise map is
invertible without its actual criterion. Relative base flatness alone does
not identify ordinary `p^*M` with `Lp^*M` when the ambient morphism is
nonflat. This coherent relatively flat sheaf theorem does not yet supply
the separate arbitrary-perfect-complex relative-Tor tier, and perfectness
over a noncoherent new ring does not imply finite cohomology there.

The exact source passed `1792125650684780000-81590` in 3.5 seconds at the
default budget. The independent arbitrary-universe
`ProperFiniteModelConsumer.lean` passed `1792125770637031000-82528`. It
checks the internally supplied lifted cover/model, one actual `P` shared
by source and every base change, installed native `Rf_*`, and the original
geometric cohomology map/native homology-mate square on the proper model.
All three inspected public suppliers use only `propext`, `Classical.choice`
and `Quot.sound`. No whole-library build was used.

The shared [Fibers](../../FiniteModel/Fibers.lean) and
[BaseChangeCriterion](../../FiniteModel/BaseChangeCriterion.lean) methods
apply directly to this internally constructed proper `D`. Independent
arbitrary-universe consumers check the original fibre dimension on literal
residue-field scalar extension (`1792126612714972000-90284`) and
invertibility/epimorphy of the original geometric map against its native
model mate for every target ring and degree (`1792126810983862000-92117`).
Neither comparison presumes that every degreewise map is invertible.

[LocalCriterion](../LocalCriterion.lean) gives the original local proper
cohomology criteria from this same constructed model. For a Noetherian
local base, proper `f`, coherent `M` and relative-flat `M`, epimorphy of the
original degree-`q` residue comparison implies arbitrary original base
change in that degree. Given epimorphy in degree `q+1`, original `H^(q+1)`
is free exactly when the degree-`q` residue comparison is epic. Its own
residue surjectivity suffices for freeness of `H^0`. No reducedness
hypothesis is imposed; the actual original residue-map hypothesis is
retained. The target ring need be neither flat nor Noetherian. Source
`1792127139611224000-95574` passed in 21 seconds at the default budget;
the independent arbitrary-universe original-map/action consumer passed
`1792127203628558000-96264`, with only the standard three axioms for all
three inspected endpoints. The separate constant-dimension Grauert
criterion retains reducedness, and a genuine open-neighbourhood statement
still needs the native residue/free-locus normalization.

[Semicontinuity](../Semicontinuity.lean) proves
`upperSemicontinuous_moduleFiberCohomologyDimension_of_proper` in every
degree for an actual proper morphism to a Noetherian affine base, coherent
`M` and relative-flat `M`. It internally constructs this same `D`; the
ordinary fibre and original structural residue action are unchanged.
No reducedness, projective embedding or comparison family is required.
Source `1792127464110134000-98959` passed in 2.7 seconds; the independent
arbitrary-universe public consumer passed `1792127490598539000-99293`.
The shared model proof and actual proper endpoint use only standard axioms.

[EulerCharacteristic](../EulerCharacteristic.lean) gives
`isLocallyConstant_moduleFiberEulerChar_of_proper`: the original intrinsic
alternating sum of ordinary fibre-cohomology dimensions is locally
constant under the same Noetherian/proper/coherent/relative-flat inputs.
It uses this same model and its actual strict bounds, with no reducedness
hypothesis or substituted numerical invariant. Source
`1792127713517360000-1604` and independent arbitrary-universe consumer
`1792127734693142000-1911` passed, with standard axioms only.
