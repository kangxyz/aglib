# Regular scalars and tensor products

[TensorProduct](TensorProduct.lean), imported as `Aglib.RingTheory.Regular.TensorProduct`, supplies `Algebra.isSMulRegular_of_baseChange_injective_of_linearEquiv`. Let `R`, `T` be commutative rings with the specified `R`-algebra structure on `T`. For a linear map `f : M →ₗ[R] R`, a coordinate equivalence `e : M ≃ₗ[R] R` and a scalar `a : R`, assume `f m = e m * a` for every `m`. Injectivity of the actual scalar-extended `f` makes `algebraMap R T a` regular in `T`.

The theorem has no flatness premise. It preserves the chosen scalar, its `algebraMap` image and the actual tensor comparison. The [tensor-map injectivity criterion](../../LinearAlgebra/TensorProduct/Map.lean) is its lower linear-algebra input; line-bundle chart regularity is a geometric consumer.
