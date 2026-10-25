> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#assemble-normal-generic-triangles-before-the-concrete-integral-closure) · [Context](original-context.md) · [Case index](README.md) · [Previous record](use-a-finite-original-unit-calculation-for-constant-direct-image-coordinates.md) · [Next record](retain-complete-product-families-through-finite-stage-factorization.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Assemble normal generic triangles before the concrete integral closure

On Lean 4.34.1 and Mathlib `d13f23b`, the first
[normal generic model](../../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteCogenerators/NormalGenericModel.lean)
source `90df91ee9a26693d0a1cbaac567e7a03483bbfb032132d5cb1100003c657a8b2`
failed in `remote-49522076a3ac4507bffb6d65c2b974bc`. It had scalar-tower
orientation and native function-field instance errors, plus a 200000-heartbeat
whnf timeout at concrete integral-closure specialization. The next failed
run `remote-b9f30b7bfd174e72a1255b5d20eb63a3` retained instance failures and a
constructor timeout; neither run supplies accepted source.

The passing implementation supplies the named native
`StructureSheaf.stalkAlgebra` and `functionField_isFractionRing_of_affine`
producers. It proves the original localization triangle at abstract R,C,L,
then assembles its complete original field-map equation and constant
trivialization at abstract R,C,K,L. Only that complete constructor receives
the actual integral closure. Typed scalar-tower equations retain the literal
structures. The canonical field point is `IsLocalRing.closedPoint Q`; default
point instance search had failed separately. The actual maps and assumptions
are preserved, and the integral closure remains possibly infinite.

Exact source
`2a46fc5b9ddbce8bd67452bf5a75993407da9dc2ef99a2f313d347560004da5d`
passed its complete frontend in `remote-8950dd65f65242898c09150d9b16957d`,
reported as 32 seconds, at unchanged standard budgets. The outer graph failed
on the separate Spectrum consumer. This validates the repaired leaf without
a benchmark, unique compiler-cause attribution or claim of a finite
normalization.

