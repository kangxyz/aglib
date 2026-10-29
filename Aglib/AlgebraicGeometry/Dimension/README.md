# Scheme dimension on covers and at actual stalks

[OpenCover](OpenCover.lean) proves
`Scheme.topologicalKrullDim_le_of_openCover` for an arbitrary uniform
`WithBot ENat` bound. The scheme and cover index retain independent universes;
there is no dimension-one or finiteness condition.

[CodimensionTwo](CodimensionTwo.lean) defines
`Scheme.SurfaceDimensionAtMostTwo`, `Scheme.CodimensionTwoPointsClosed` and the
actual subtype `Scheme.CodimensionTwoPoint`. It proves closedness of every
stalk-dimension-two point from the uniform stalk upper bound. The proof uses
strict antitonicity of finite coheight. The K-theory-specific `ClosedPoint`
compatibility alias remains downstream. The existing
[stalk dimension provider](../Stalk/Dimension.lean) still owns the equality
between scheme dimension and the supremum of actual stalk dimensions.

[FlatDVR](FlatDVR.lean) retains
`Scheme.FlatDVR.ProperFlatDVRGenericCurveDimension` as an explicit proposition
family. It asks for dimension two of an integral proper flat scheme over a
DVR with its literal smooth relative-dimension-one generic pullback. This file
provides no term of the family. Its original statement has no excellence or
perfect-residue-field assumption; a future restricted theorem must retain any
extra premise and cannot inhabit the unrestricted family without a proof.

[QuasiFiniteSurjective](QuasiFiniteSurjective.lean) proves
`Scheme.Hom.strictMono_of_locallyQuasiFinite`: a locally quasi-finite morphism is
strictly monotone for Mathlib's specialization order on schemes, because its
fibres are discrete. A locally quasi-finite `f : X ⟶ Y` with closed image and
irreducible `Y` is surjective when some `x : X` has
`dim 𝒪_{Y,f x} ≤ dim 𝒪_{X,x} < ∞`
(`Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top`);
the endomorphism form
`Scheme.Hom.surjective_of_locallyQuasiFinite_of_isClosed_range_of_apply_eq` needs
an irreducible locally Noetherian `X` and a fixed point. Stalk dimensions enter
as coheights (Mathlib's `ringKrullDim_stalk_eq_coheight`); no bound on `dim X`
or `dim Y` and no going-up theorem is used. Consumer:
[Group/MultiplicationSurjective](../Group/MultiplicationSurjective.lean).

The native curve and model interfaces consume these bounds and conditions.
