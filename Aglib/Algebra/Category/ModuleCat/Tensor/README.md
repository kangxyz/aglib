# Scalar extension and tensor products

[ScalarExtension](ScalarExtension.lean), imported as `Aglib.Algebra.Category.ModuleCat.Tensor.ScalarExtension`, constructs `ModuleCat.scalarExtensionTensorIso` and `scalarExtensionTensorNatIso`. Along the specified commutative-ring map, tensoring two scalar-extended modules agrees with scalar extension of their original tensor product.

The pure-tensor forward/inverse formulas and naturality use the actual extension-of-scalars functor. Flatness is not needed for this tensor isomorphism; it is a separate hypothesis when a consumer asks for exactness. Scheme pullback tensor and coefficient base-change maps use these original scalar comparisons.
