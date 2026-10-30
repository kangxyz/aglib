# Abelian schemes and field specializations

This family uses native group schemes over their actual base, without a new
object model. Current field-specific results live in `OverField/`; they do
not assert relative results over arbitrary bases. General group, Picard and
curve constructions remain in [Group](../Group/README.md),
[Picard](../Picard/README.md) and [Curves](../Curves/README.md).

[Cube](OverField/LineBundle/Cube.lean), [Square](OverField/LineBundle/Square.lean),
[Multiplication](OverField/LineBundle/Multiplication.lean) and
[Symmetric](OverField/LineBundle/Symmetric.lean) use original Picard classes
and maps for projective geometrically integral field groups. The cube equation
applies to all test schemes, including nonreduced ones. Multiplication retains
its binomial formula, with symmetric exponent `n²` and antisymmetric exponent
`n`, including zero and one.

[Morphism](OverField/LineBundle/Morphism.lean) classifies the original
translated line-bundle family as `φ_L` using the supplied fppf Picard
representative on locally Noetherian tests; it gives the group homomorphism and
factorization through the same identity component. [FamilyFormula](OverField/LineBundle/FamilyFormula.lean),
[KernelClass](OverField/LineBundle/KernelClass.lean),
[AmpleKernel](OverField/LineBundle/AmpleKernel.lean) and
[BaseChange](OverField/LineBundle/BaseChange.lean) retain the actual family,
scheme-valued kernel, ample finite-kernel result and field base-change maps.

[Poincare](OverField/Dual/Poincare.lean) pulls the same universal rigidified
pair back to the Picard identity component, with both unit trivializations and
pullback coherence on arbitrary tests. Classification uses the locally
Noetherian tests represented by the supplied Picard object.
[Positive multiplication](OverField/Multiplication/Finite.lean) is finite,
flat and surjective for projective geometrically integral commutative field
groups at every positive level, including characteristic-divisible levels.
Numerical degree and rank, dual properness and smoothness, biduality, Cartier
duality, theta, principal polarization and Weil pairing remain separate.
