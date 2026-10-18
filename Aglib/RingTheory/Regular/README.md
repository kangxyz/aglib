# Regular scalars and tensor products

[TensorProduct](TensorProduct.lean), imported as `Aglib.RingTheory.Regular.TensorProduct`, supplies `Algebra.isSMulRegular_of_baseChange_injective_of_linearEquiv`. Let `R`, `T` be commutative rings with the specified `R`-algebra structure on `T`. For a linear map `f : M →ₗ[R] R`, a coordinate equivalence `e : M ≃ₗ[R] R` and a scalar `a : R`, assume `f m = e m * a` for every `m`. Injectivity of the actual scalar-extended `f` makes `algebraMap R T a` regular in `T`.

The theorem has no flatness premise. It preserves the chosen scalar, its `algebraMap` image and the actual tensor comparison. The [tensor-map injectivity criterion](../../LinearAlgebra/TensorProduct/Map.lean) is its lower linear-algebra input; line-bundle chart regularity is a geometric consumer.

[PrimeAvoidance](PrimeAvoidance.lean), imported as `Aglib.RingTheory.Regular.PrimeAvoidance`,
supplies `associatedPrimes.exists_forall_isSMulRegular`. Over an infinite field `k`, take
finitely many `k`-linear maps `λⱼ : V → Aⱼ` into Noetherian `k`-algebras and finite
`Aⱼ`-modules `Mⱼ`. If no associated prime of any `Mⱼ` contains `λⱼ V`, one `v ∈ V` makes every
`λⱼ v` a nonzerodivisor on `Mⱼ`. The inputs are Mathlib's finiteness of associated primes, the
description of zero divisors as their union, and the fact that a vector space over an infinite
field is not a finite union of proper subspaces. The general hyperplane of Mumford's bound
(`Cohomology/Projective/Regularity/Mumford/InfiniteField`) consumes it.
