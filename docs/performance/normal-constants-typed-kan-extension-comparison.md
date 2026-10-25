> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#normal-constants-typed-kan-extension-comparison) · [Context](original-context.md) · [Case index](README.md) · [Previous record](cancel-the-original-unit-before-supplying-concrete-section-rings.md) · [Next record](ringed-coefficient-equivalence-typed-adjunction-unit-boundary.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Normal constants: typed Kan-extension comparison

Typed Kan-extension comparison for the original generic unit

Affected declaration
AlgebraicGeometry.Scheme.EtaleCohomology.NormalConstants.isIso_representedGenericUnit
in Constructible/NormalConstants/Represented.lean.
Lean 4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612;
private base 175a8ee20860f4ad7470cc3b043f618502380457.

Observed failed scope
remote-66083d8753994721b679a72634c53776, snapshot
5d168a61c59681d79109a8395e3a63841f6e8c4daa17a22f8e9f34245a5ab652,
Represented.lean SHA 0bb5d3986ed4b8454f8d3eb53d7d469934a5d81e0f9f7babdde960114998e363.
The concrete theorem transported the sheafification-unit isomorphism with
NatTrans.isIso_app_iff_of_iso applied to representedPresheafBaseChangeIso j H.
It exceeded the standard 200000 heartbeats at isDefEq, line 175:38, and the
whole declaration reported a whnf timeout. The run did not accept the module.

Validated repair
A private theorem isIso_unit_of_leftKanIso takes variable source/target schemes,
coefficient sheaves, a typed native Lan comparison iso, the actual restriction
arrow, its original factorization equation, and invertibility of that arrow.
Cancellation and the sheafification step stay inside this variable-map theorem.
The latter step transports Presheaf.IsSheaf through the comparison and applies
isIso_toSheafify, instead of transporting the natural-transformation component
at the fully expanded concrete Kan extension. The concrete represented theorem
supplies exactly representedPresheafBaseChangeIso, representedBaseChangeUnit and
the native descOfIsLeftKanExtension_fac equation. No map, hypothesis, resource
ceiling or mathematical statement changed.

Actual successful scope
remote-564eb185f0af40438bea720bf0a3e23b, snapshot
b63b61c86b7615e38a8191bc30b28bdef649f1f0ba58c402933a2255a376558a,
accepted the exact Represented leaf, SHA
7203bf4f2258ad998327f9d1be05372b08bcc99fbd3c9f8b246abccd92a2adad,
in a reported 15 seconds, with no diagnostics in that leaf, at 200000 heartbeats.
The same run failed in the root NormalConstants leaf on unrelated style and
instance lookup; it is successful evidence only for Represented. The final
root consumer subsequently compiled in remote-91552d915c764abd8454c7c6b4be047d,
snapshot 75bfa8baf56185dc212317b1065358c550058c385ccd014f11e5a1ffd9372524:
one fresh root frontend, exit 0, no diagnostics, reported 6.3 seconds.
The accepted Represented artifact was retained; it was not rebuilt.

This validates a proof-representation boundary. It does not isolate a compiler
cause or establish a matched speedup. No profiling, replay or benchmark was run.
Logs are retained under the adjacent remote-runs/<run-id>/build.log paths.


