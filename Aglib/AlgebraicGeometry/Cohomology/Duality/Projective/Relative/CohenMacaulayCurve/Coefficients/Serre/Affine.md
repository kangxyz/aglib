# The original affine coefficient model

[Affine.lean](Affine.lean) works over a field `k` with an arbitrary specified
`V : ModuleCat k`. There is no finiteness, dimension, CM or rank condition
on this coefficient. The actual closed embedding data used by the affine
Hom wrappers and its original structural scalar map are retained.

The native coefficient isomorphism is
`κ : Γ(Spec k, tilde V) ≅ V`, the inverse of
`tilde.toTildeΓNatIso.app V`. The affine structural-section isomorphism gives
`c_V : G(tilde V) ≅ V` for the original structural global-sections functor
`G`. Quasicoherent affine acyclicity makes its original single unit on
`tilde V` invertible. `cmCurveCoefficientSerreAffineTargetIso` is exactly
that inverse unit followed by `single₀(c_V)`, and its unit equation is
proved by inverse cancellation.

`cmCurveCoefficientSerreModuleHom` uses the original global-sections
composition comparison, the actual fully faithful shifted preimage, the
same right-derived functor, and this coefficient target. Its application,
source-composition and degree-zero laws are proved from the shared native
constructors. The original affine derived-Hom comparison and its actual
integer-reindex homology extraction agree with that model. The original
coefficient square is proved through the original single units; it is not
an extra comparison input. Native shifts, addition comparisons and signs
are kept throughout.

`cmCurveCoefficientEvaluationPacket` permits different structural source
and coefficient target. Its formula uses the native single preimage and
the original zero-shift arrow. The concrete evaluator uses the original
structural derived unit and the actual `κ`; its output is in `V`.
`cmCurveCoefficientSerreModuleHom_unit` proves the module-valued map on the
original structural section one equals this same evaluator for every
actual degree-zero derived arrow. The proof uses the published original
structural-unit pushforward law, original single-unit naturality, native
fully faithful single/homology normalization and the actual affine
coefficient map. It does not choose a new trace or an identification V≅k.

The intended coefficient-valued curve comparison consumes this arbitrary-module
provider at its actual own-homology canonical module. This child imports the
source-only unit normalization and generic single/shift tools. It does not
supply a coefficient-valued duality or pairing theorem.

The native tilde isomorphism is instantiated at the explicit ring object
`CommRingCat.of k`; its coefficient remains the literal `V`. The displayed
module-Hom application formula uses the same coefficient target as its
definition. Its degree-zero proof keeps the actual Plus preimage endpoints
explicit. Native `singleFunctorιIso` components then normalize the source
`k` and target `V` independently before homology/preimage cancellation.
The raw original arrow is retained by a proved identity, rather than an
orientation of `V`.
