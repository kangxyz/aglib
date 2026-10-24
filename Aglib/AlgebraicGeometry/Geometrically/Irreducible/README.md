# Geometric irreducibility under field extension

The directory extends Mathlib's `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`, whose
`GeometricallyIrreducible q` asks irreducibility of every base change `pullback q (Spec K ⟶ Spec k)`
along a field `K` in the universe of `k` (Stacks 0365). Declarations are in
`AlgebraicGeometry.Scheme.Geometrically`.

[FieldExtension](FieldExtension.lean): for `q : Y ⟶ Spec k` and fields `k ⊆ K ⊆ L` with
`IsScalarTower k K L`, irreducibility of `Y_L` implies irreducibility of `Y_K`
(`irreducibleSpace_pullback_of_irreducibleSpace_pullback_of_isScalarTower`; `Y_L ≅ (Y_K)_L` maps
onto `Y_K`, the surjectivity step of Stacks 054P). If `Y_K` is irreducible for every algebraically
closed extension `K` of `k`, then `q` is geometrically irreducible
(`geometricallyIrreducible_of_forall_isAlgClosed`, through
`geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` and `AlgebraicClosure K`). The
criterion quantifies over all algebraically closed extensions; the stronger form with one algebraic
closure of `k` is not stated. Consumer:
[Group/IdentityComponent/FiniteType](../../Group/IdentityComponent/FiniteType.lean).
