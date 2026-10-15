# Selected exact structures and exact functors

`CategoryTheory.ExactCategory.ExactStructure C` selects conflations in a preadditive category with finite biproducts. It carries actual kernel/cokernel universal properties and the identity, composition and relevant pushout/pullback axioms. It requires no ambient abelian structure or arbitrary-limit existence.

| Result/interface | Conditions and conclusion |
| --- | --- |
| `abelianExactStructure_conflation` | In an abelian category, the standard selected conflations are exactly the actual short exact sequences. |
| `ExactFunctor.map_inflation`, `map_deflation`, `map_isPullback` | An actual additive functor preserving the chosen conflations transports inflation/deflation and the stated exact pullback squares. |
| `ExactStructure.ofEquivalence` | An actual equivalence transports the chosen exact structure; `equivalenceExactFunctor` and its inverse are the corresponding exact functors. |
| `ExactSubcategory.exactStructure` / `exactInclusion` | Containing zero, repleteness and extension closure give the inherited exact subcategory and exact inclusion. Arbitrary ambient kernel/cokernel closure is not required. |

All names in the table are under `CategoryTheory.ExactCategory`. Import `Aglib.CategoryTheory.ExactCategory.Basic` for objects, [Abelian](Abelian.lean) for the standard structure, [Functor](Functor.lean) for exact functors, [Equivalence](Equivalence.lean) for transport and [Subcategory](Subcategory.lean) for inheritance. [Isomorphisms](Isomorphisms.lean), [Composition](Composition.lean), [BaseChange](BaseChange.lean) and [MatrixDeflation](MatrixDeflation.lean) give the actual square/biproduct calculations.

This `ExactFunctor` is the functor between selected exact structures, distinct from other native exact-functor notions. Consumers are [small models](../SmallModel/README.md), finite modules, ambient module sheaves, coherent sheaves and the exact category of finite locally free sheaves.
