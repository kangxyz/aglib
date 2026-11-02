# Inverse-trace pullback on an actual isomorphism open

Source: [Restriction.lean](Restriction.lean).

Import `Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Restriction`.
The namespace is `AlgebraicGeometry.Scheme.Modules`.

`ordinaryTracePullback_isIso_of_isIso_restrict` takes arbitrary original
schemes, their actual qcqs morphism f, one quasicoherent source coefficient
M, any target coefficient N, an invertible actual trace f_*M -> N, and a
target open U where the SAME f restricts to an isomorphism. It proves that
the SAME open pullback of ordinaryTracePullback f tau is invertible.
No target-coefficient quasicoherence, Noetherianity, finiteness, flatness of
f, properness, integrality, normality, dimension or canonical datum is used.

The original square is `isPullback_morphismRestrict f U`. The existing
flat qcqs base-change theorem applies along U.ι to its original ordinary
mate. The existing closed-immersion counit theorem applies to the actual
isomorphism f|U. The original inverse-trace base-change equation then
expresses the SAME restricted map as a composite of these isomorphisms.

This body is extracted once from PointBlowupGeneration, whose entire public
telescope and actual centred-generation argument remain unchanged. Its
point-centre complement geometry stays in the higher consumer; only the
generic restriction calculation is replaced by a thin call.

This focused leaf lives beside the existing generic inverse-trace and
ordinary degree-zero base-change owners. Its imports contain no canonical
object, projective geometry or surface theorem. Moving the result into
Modules would create an upward cohomology import or demand unrelated owner
moves; neither is introduced here. No new pullback or trace is constructed.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupGeneration](PointBlowupGeneration.md).
