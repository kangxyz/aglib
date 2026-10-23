# Regular locality across a rank-one kernel

[RankOneKernel.lean](RankOneKernel.lean) supplies
`IsRegularLocalRing.of_surjective_ker_freeRankOne f hf e`.
Here `R` is a Noetherian local ring, `S` is a regular local ring, `f : R →+* S`
is surjective, and `e : RingHom.ker f ≃ₗ[R] R` is a rank-one free presentation
of its actual kernel. The ring universes are independent.

The existing
[`Ideal.ideal_exists_regular_generator`](../Ideal/RegularPrincipal.lean)
provides a nonzerodivisor generating this kernel. The actual equivalence
`f.quotientKerEquivOfSurjective hf` transports regular locality of `S` to the
quotient. The existing
[`IsRegularLocalRing.of_quotient_span_singleton`](QuotientLift.lean)
then proves regular locality of `R`. No new principal-generator implementation,
domain assumption, coefficient field or condition on the square of the maximal
ideal is introduced.

The current consumer is the
[Cartier closed-immersion stalk theorem](../../AlgebraicGeometry/IdealSheaf/Cartier/RegularQuotient.lean).
Source basis: Aglib `22f7532679eec4295167fcf885cf8b1b0981d899`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. Native compilation
is coordinated by the root task.
