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
[SourcePullback](OverField/LineBundle/SourcePullback.lean) proves the whole
translated-family class formula on arbitrary tests and the contravariant
source-group pullback formula for the original represented line-bundle
morphism and its same identity-component restriction. The displayed source
geometry and supplied representative hypotheses remain explicit.

[Poincare](OverField/Dual/Poincare.lean) pulls the same universal rigidified
pair back to the Picard identity component, with both unit trivializations and
pullback coherence on arbitrary tests. Classification uses the locally
Noetherian tests represented by the supplied Picard object.
[Positive multiplication](OverField/Multiplication/Finite.lean) is finite,
flat and surjective for projective geometrically integral commutative field
groups at every positive level, including characteristic-divisible levels.
[Rank](OverField/Multiplication/Rank.lean) gives the original multiplication
and its native kernel locally free rank `n^(2*d)` over every field for `n > 0`,
where `d` is the identity cotangent dimension, assuming smoothness. This
includes characteristic-divisible levels. [Torsion](OverField/Multiplication/Torsion.lean)
gives geometric degree, geometric torsion and native kernel point counts at
unit levels, and a noncanonical equivalence with `(ZMod n)^(2*d)` using
all divisor-level counts. No canonical or Galois-equivariant basis is asserted.
Dual properness and smoothness remain conditional as described below; biduality,
Cartier duality, theta, principal polarization and Weil pairing remain separate.

[Translation](OverField/LineBundle/Translation.lean) retains parameter-valued
translation and whole rigidified-isomorphism coherence, including nonreduced
tests; classification uses the supplied representation on locally Noetherian
tests. Pullback of a line bundle by source-group inversion preserves its
line-bundle morphism; this is distinct from dualizing the bundle and from
parameter inversion: dualizing the bundle inverts `φ_L`, as does precomposing
`φ_L` with source-parameter inversion. No general nonreduced-parameter
rigidity is asserted.

[AmpleCriterion](OverField/LineBundle/AmpleCriterion.lean) proves ampleness of
an original line bundle with a nonzero global section and finite actual
`φ_L` kernel on a projective geometrically integral commutative group over an
algebraically closed field. It does not require dual smoothness or the H¹
bound. The actual ample `φ_L` is finite without that bound or source smoothness.

[Dual dimension](OverField/Dual/Dimension.lean),
[properness](OverField/Dual/Properness.lean),
[smoothness](OverField/Dual/Smoothness.lean),
[projectivity](OverField/Dual/Projectivity.lean) and
[isogeny](OverField/Dual/Isogeny.lean) give criteria for the same supplied
Picard representative and identity component over any field. For the proper
smooth geometrically integral source and an actual ample bundle, the original
inequality `finrank H¹(O_A) ≤ finrank Cotangent(unit_A)` is retained in the
conclusions on dual properness, smoothness, dimension and finite-flat
surjectivity of `φ_L`; the H-projective source version also gives geometric
integrality and projectivity. The coherent-H¹ bound itself remains open.

[Dual homogeneity](OverField/Dual/Homogeneity.lean) assumes the original
proper geometrically integral field group `A` and the same supplied `P,R`
with locally finite-type separated representative, and additionally that its
actual identity component `D` is proper and geometrically integral. On
arbitrary tests the original universal translation difference equals the
pullback of its actual base evaluation; the normalized rigidified pair is
trivial. [Dual multiplication](OverField/Dual/Multiplication.lean) proves
that original source pullback by `[n]` is `[n]` on this same `D` for every
natural `n`, with contravariant composition and field-base-change laws.
These results do not supply the separate coherent-H¹ bound or these dual
geometry hypotheses.

[Bidual](OverField/Dual/Bidual.lean) constructs the original map `h_A`
by transposing the selected Poincaré bundle and classifying it through a
second supplied Picard representative `Q,S` of the same `D`. For a proper
geometrically integral field group `A`, it gives the original component and
pointed maps; the component construction assumes `Q` locally of finite type,
and its group-map law additionally assumes `Q` separated. It proves the
original contravariant naturality and `h_A ≫ (φ_L)^∨ = φ_L` under their
stated inputs. No properness or geometric integrality of `D`, coherent H¹
bound, bidual isomorphism or dual-isogeny degree formula is asserted.
