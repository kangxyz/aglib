> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#retain-complete-product-families-through-finite-stage-factorization) · [Context](original-context.md) · [Case index](README.md) · [Previous record](assemble-normal-generic-triangles-before-the-concrete-integral-closure.md) · [Next record](pass-the-preservation-dictionary-of-an-equivalence-explicitly.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Retain complete product families through finite-stage factorization

The original
[Spectrum](../../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteCogenerators/Spectrum.lean)
assembly encountered a dependent rewrite motive, a categorical `Pi.map` name
collision and product projections retaining different constant-cocone heads.
Source `64f138c7d25789632b4ccd8aebfd8fe5a4d85dc6392565c8ffcf48c8137b1465`
also timed out at 200000 heartbeats in `remote-02dc218e3235421c94394cbf8a1605e1`,
while an ordinary projection type error remained. The later ae862b49 source
reported only a calc Trans inference error, without a timeout. These mixed
repairs do not identify one cause of the earlier cost.

The final proof names the actual `normalModelTargets` family and its original
`normalModelProduct_π` equation. Typed associativity, `congrArg` and `Eq.trans`
transport those complete equations; `CategoryTheory.Limits.Pi.map` is qualified.
The product-monicity factorization is proved at abstract categorical objects
and supplied with the entire actual cocone and model packet. This preserves
all finite values, actual stage arrows and the original mono.

Source `b19fec9aba152326f896fda0e5665155f127a6110f796388bc90f10dbb7d0506`
passed its complete frontend in `remote-9c333911ae764c3fa4aa3ffb6ae96062`.
Its Affine consumer initially failed on another projection normalization.
The same typed equation boundary repaired exact Affine source
`7cca91d19ee404a79ec80ce7c928e89a5b046d4c8c7bba30742996bd69f03c3c`,
which passed `remote-1848273a3a744f19ba71b722e32c481c`: one fresh frontend,
no diagnostics, 5.864 seconds between compiler events. Ordinary budgets were
unchanged; these existing observations are not a controlled speedup, profiling
experiment or broader verification cycle.

