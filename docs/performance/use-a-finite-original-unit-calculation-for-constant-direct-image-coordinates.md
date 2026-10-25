> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#use-a-finite-original-unit-calculation-for-constant-direct-image-coordinates) · [Context](original-context.md) · [Case index](README.md) · [Previous record](keep-the-original-universal-exchange-test-at-a-shared-data-head.md) · [Next record](assemble-normal-generic-triangles-before-the-concrete-integral-closure.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Use a finite original-unit calculation for constant direct-image coordinates

In the finite-constant
[represented-coordinate supplier](../../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteCogenerators/AffineIntegralConstants/RepresentedSections.lean),
run `remote-442a6e3ab1a34db3a105414977b08fb5` diagnosed a potentially looping
simp rule and exceeded maximum recursion depth. The original calculation
combined forward `Functor.map_comp` and associativity with reverse
`Functor.map_comp_assoc`. This was a rewrite loop; it was not a measured
heartbeat timeout.

The repair is a finite calculation using forward functor composition, the
original adjunction-unit naturality equation, and explicitly typed
identity-map equations transported by `congrArg`. Projection lemmas retain
the exact original `Scheme.Etale.forget` object heads. The final residual
projection mismatch in `remote-6039f2c31878477ca53093e34b01bd76` was repaired
at that same head. No recursion or heartbeat budget was raised, and the
original maps and mathematical assumptions were preserved.

Exact source
`458ea48f66e37deba72898fd309dde62d9bbc5a57d77834b9a720c7c2a6800da`
passed `remote-df229d88e13c44a58e0467cc3745c13e`: one successful frontend,
no diagnostics and 15.27 seconds for the build action. Lean and Mathlib
remain at the pinned versions above. These existing observations do not
supply a benchmark, profiling attribution or broader mathematical closure.

