# Open-free generators and finite local lifting

[OpenFreeFunctor](OpenFreeFunctor.lean), imported as `Aglib.AlgebraicGeometry.Modules.Generators.OpenFreeFunctor`, constructs actual open-free module sheaves and their functor of opens. `openFreeHomEquiv` represents actual sections, with naturality in both coefficient sheaves and opens. [OpenFreeStalk](OpenFreeStalk.lean) compares actual stalks with the free stalk module on point-membership data and proves the original comparison naturality.

[LocalLifting](LocalLifting.lean) gives `Scheme.Modules.exists_finite_local_lifts`: for an actual locally surjective map, finitely many sections admit simultaneous lifts on one neighborhood. Finiteness of the family permits a common neighborhood. The actual [epimorphism/local-surjectivity](../Epimorphisms.lean) result supplies that hypothesis for module-sheaf epimorphisms.

Focused imports are these three leaves. [Local splitting of vector bundles](../LocallyFree/README.md), flat generators and scheme injective Cech exactness use these real section/stalk maps. No global basis or projectivity assumption is inferred from a local lift.
