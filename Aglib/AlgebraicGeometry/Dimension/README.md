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

The native curve and model interfaces consume these bounds and conditions.
