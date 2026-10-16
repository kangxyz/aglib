# Tensor-product maps and injectivity

[Map](Map.lean), imported as `Aglib.LinearAlgebra.TensorProduct.Map`, supplies `LinearMap.lTensor_injective_of_equiv_square`. Actual source and target linear equivalences in a commuting square transport injectivity after tensoring by any module over the commutative base ring.

The coefficient object is an arbitrary module; flatness, finiteness and an algebra structure are not premises. [Regular scalars under tensor extension](../../RingTheory/Regular/TensorProduct.lean) and affine module pullback comparisons consume this map criterion.
