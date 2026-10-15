# Original Ext maps and acyclic comparison

[AcyclicComparison](AcyclicComparison.lean) defines
`Functor.extPrecompMap` as the original `Ext.mapExactFunctor` followed by
precomposition with a specified original source morphism. Its degree-zero
formula and compatibility with Yoneda composition are proved.

`Functor.extPrecompMap_bijective_of_acyclic_injectives` needs an exact
additive functor, enough injectives in its source, a degree-zero bijection,
and actual positive Ext acyclicity of the images of source injectives for
the specified target source object. It proves bijectivity of that original
comparison in every degree. `extPrecompAddEquivOfAcyclicInjectives` packages
the same map as an additive equivalence. The functor is not required to
preserve injective objects or to be fully faithful.

The unit-module/additive-sheaf cohomology comparison uses this criterion
with the actual scalar-forgetting functor and its proved flasque injective
images. No scheme or quasicoherence hypothesis occurs in this lower family.
