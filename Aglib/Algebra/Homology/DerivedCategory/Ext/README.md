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

[Quotient](Quotient.lean) works over a commutative ring `R` and proves that
original Ext from `R/I` is annihilated by `I` and constructs its native
quotient-ring module action explicitly.
That action equals original Yoneda precomposition with multiplication on
`R/I`, the action used by scalar coinduction. All degrees and arbitrary
coefficients are included, without regularity, finiteness or Noetherianity.
The module action is not installed as a global instance. Its first consumer
is the [actual principal-ideal Koszul calculation](../../Koszul/Single/Ext/Ideal.lean).
Source and public consumer passed `1792127465949194000-98994` and
`1792127498584479000-99373` with only the standard three axioms.

[SingleShift](SingleShift.lean) proves that maps from the native same-degree
single of a projective object to a positive integer shift of any coefficient
single are zero. It retains the original single-functor shift and localization
comparisons. Only projectivity of the displayed source object is required;
there is no `HasExt`, enough-projectives, enough-injectives or coefficient
projectivity premise. Concentrated finite-free derived global sections in
relative projective Serre duality are a current consumer.
