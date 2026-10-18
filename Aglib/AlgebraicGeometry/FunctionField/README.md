# Function fields and generic maps

[Basic](Basic.lean) uses the canonical `X.fromSpecStalk (genericPoint X)` and Mathlib function field. For an integral scheme it proves the actual image point, nonempty-open preimages, quasi-compactness and the specified section/germ comparison. No normality, Noetherianity or dimension bound is used.

[Normalization](Normalization.lean) proves that the generic inclusion of an integral scheme with integrally closed stalks has the original scheme as normalization. For a smooth structural morphism `p : Y ⟶ X` and an integral structural morphism `q : Z ⟶ X` (`IsIntegralHom q`), it extends an actual generic-fibre map uniquely to an `X`-morphism `Y ⟶ Z`. No intrinsic integrality condition on `Y` or `Z` is imposed. [Finite-etale generic restriction](../Morphisms/FiniteEtale/GenericFiber.lean) consumes this general extension.

These source migrations retain their recorded R5 inputs and canonical maps.
Source correspondence and native validation have separate evidence boundaries;
see the [recorded checkpoints](../../../doc/WORK_PLAN.md).

[Map](Map.lean) constructs actual dominant pullback and structural field constants from generic stalks and global germs, with their original naturality equations. [BaseChange](BaseChange.lean) transports that same map along field base change when the actual pullback remains integral. [GenericFiber](GenericFiber.lean) constructs the actual generic-fibre lift and proves it invertible for a finite dominant map of integral schemes, without Noetherianity, normality, separability or dimension assumptions. No second generic inclusion or finite-generic-fibre family predicate is defined.
