# Selected exact structures and exact functors

`CategoryTheory.ExactCategory.ExactStructure C` selects conflations in a preadditive category with finite biproducts. It carries actual kernel/cokernel universal properties and the identity, composition and relevant pushout/pullback axioms. It requires no ambient abelian structure or arbitrary-limit existence.

| Result/interface | Conditions and conclusion |
| --- | --- |
| `abelianExactStructure_conflation` | In an abelian category, the standard selected conflations are exactly the actual short exact sequences. |
| `ExactFunctor.map_inflation`, `map_deflation`, `map_isPullback` | An actual additive functor preserving the chosen conflations transports inflation/deflation and the stated exact pullback squares. |
| `ExactFunctor.map_isPushout` | A displayed pushout `IsPushout i f g j` is preserved when its first input `i` is an inflation for the source exact structure. The admissibility premise is retained. |
| `ExactStructure.ofEquivalence` | An actual equivalence transports the chosen exact structure; `equivalenceExactFunctor` and its inverse are the corresponding exact functors. |
| `ExactSubcategory.exactStructure` / `exactInclusion` | Containing zero, repleteness and extension closure give the inherited exact subcategory and exact inclusion. Arbitrary ambient kernel/cokernel closure is not required. |

All names in the table are under `CategoryTheory.ExactCategory`. Import `Aglib.CategoryTheory.ExactCategory.Basic` for objects, [Abelian](Abelian.lean) for the standard structure, [Functor](Functor.lean) for exact functors, [Equivalence](Equivalence.lean) for transport and [Subcategory](Subcategory.lean) for inheritance. [Isomorphisms](Isomorphisms.lean), [Composition](Composition.lean), [BaseChange](BaseChange.lean) and [MatrixDeflation](MatrixDeflation.lean) give the actual square/biproduct calculations.

[FunctorPushout](FunctorPushout.lean), imported as `Aglib.CategoryTheory.ExactCategory.FunctorPushout`, owns `ExactFunctor.map_isPushout`. Source and target are preadditive categories with finite biproducts and their supplied exact structures; their object and morphism universes are independent. The result concerns the four actual functor images of the displayed square. Its proof applies exactness to the square's signed biproduct cokernel sequence and then uses the canonical biproduct comparison. It does not require an ambient abelian category.

This `ExactFunctor` is the functor between selected exact structures, distinct from other native exact-functor notions. Consumers are [small models](../SmallModel/README.md), finite modules, ambient module sheaves, coherent sheaves and the exact category of finite locally free sheaves.

[Small](Small.lean), imported as `Aglib.CategoryTheory.ExactCategory.Small`, owns `CategoryTheory.ExactCategory.SmallExactCategory`. In universe `u`, it bundles `Obj : Type u`, `Category.{u}`, preadditivity, finite biproducts and a selected `ExactStructure`; the bundle has type `Type (u + 1)`. Its morphisms are the existing exact functors, with their actual identity and composition. `ExactFunctor.ext_toFunctor` identifies exact functors whose underlying functors agree. This bundle carries no K-group data. It is distinct from [SmallModel transport](../SmallModel/README.md), which transports a given category and exact structure through a chosen equivalence.

[KernelClosed](KernelClosed.lean) defines `ExactStructure.IsKernelClosed P`
for the selected conflations. Membership of both the middle and last objects
implies membership of the first; arbitrary admissible-subobject closure is a
different and stronger condition. Bounded acyclic cycle closure consumes this
interface for the standard exact structure of an abelian category.
