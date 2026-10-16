# Regular scalars and tensor products

[TensorProduct](TensorProduct.lean), imported as `Aglib.RingTheory.Regular.TensorProduct`, supplies `Algebra.isSMulRegular_of_baseChange_injective_of_linearEquiv`. A specified coordinate equivalence of an arbitrary module with the base ring and injectivity of the actual scalar-extended linear map make the displayed scalar image regular in the target algebra.

The theorem has no flatness premise. It preserves the chosen scalar, its `algebraMap` image and the actual tensor comparison. The [tensor-map injectivity criterion](../../LinearAlgebra/TensorProduct/Map.lean) is its lower linear-algebra input; line-bundle chart regularity is a geometric consumer.
