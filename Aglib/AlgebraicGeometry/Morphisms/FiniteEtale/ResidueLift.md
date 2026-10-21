# Finite etale residue base change

[ResidueLift.lean](ResidueLift.lean) proves that the actual functor

```lean
Scheme.FiniteEtale.baseChange (Scheme.LocalRing.residueSpecMap R)
```

is faithful and essentially surjective for every `R : Type u` with
`[CommRing R] [IsLocalRing R]`. It maps the native finite-etale cover category
of `Spec R` to that of `Spec (IsLocalRing.ResidueField R)`. No Henselian,
Noetherian, excellent, connectedness or reducedness assumption is imposed.

## Actual object lifting

The namespace `AlgebraicGeometry.Scheme.FiniteEtale` provides:

- `exists_spec_residue_pullback`: for a supplied finite etale residue cover
  `Y`, an actual `A : Type u` with commutative ring and `R`-algebra structures,
  `Module.Finite R A`, `Algebra.Etale R A`, and a morphism
  `g : Y.obj.left ⟶ Spec A` such that
  `IsPullback g Y.obj.hom (Spec.algebraMap R A) (LocalRing.residueSpecMap R)`.
- `exists_spec_residue_lift`: the resulting isomorphism in `Over (Spec k)`,
  from the literal pullback of `Spec A` to the original cover, where
  `k = IsLocalRing.ResidueField R`.
- `exists_residue_baseChange_iso`: the comparison packaged in the original
  finite-etale full subcategory.
- `residueSpecMap_baseChange_essSurj`: the resulting `Functor.EssSurj`
  instance for the displayed functor.

The proof first uses the actual affine coordinate ring `B = Γ(Y.obj.left, ⊤)`.
Its scalar map is the native one induced by `Y.obj.hom`, provided by
`Scheme.AffineBaseChange.coordinateAlgebra`. The theorem
`isoSpec_inv_over` retains that structural map. The algebraic producer
`IsLocalRing.exists_finite_etale_residue_lift_of_etale` supplies an actual
finite etale `A` and a `k`-algebra equivalence `e : k ⊗[R] A ≃ₐ[k] B`.

Write `a : A →+* B` for `e.toRingHom.comp includeRight.toRingHom`. The native
`Spec.isPullback_of_tensorEquiv` compares `Spec B` with the literal pullback,
retaining both projections. Transport by the original scheme's `isoSpec`
gives `g = Y.obj.left.isoSpec.hom ≫ Spec.map a`. Its opposite edge is
`Y.obj.hom` itself. `IsPullback.isoPullback` supplies the over-base
isomorphism; no substitute fibre is assumed.

## Faithfulness and the stronger uniqueness theorem

`Scheme.Hom.eq_of_residue_pullback_eq` takes a universally closed
`p : X ⟶ Spec R`, a formally unramified, locally finite-type
`q : Y ⟶ Spec R`, and maps `f g : X ⟶ Y` whose composites with `q` are `p`.
Equality after precomposition with the actual projection
`pullback.fst p (LocalRing.residueSpecMap R)` implies `f = g` as scheme
morphisms, including their structure-sheaf maps.

The diagonal of `q` is an open immersion. Pulling it back along `(f, g)` gives
an open equalizer in `X` containing the entire residue fibre. If its closed
complement were nonempty, its image under `p` would be a nonempty closed subset
of the local spectrum, hence contain the closed point. The pullback carrier
theorem then produces a point of the residue fibre in that complement, a
contradiction. Thus the equalizer is a surjective open immersion and an
isomorphism. Separatedness of `q` is unnecessary.

`Scheme.FiniteEtale.residueSpecMap_baseChange_faithful` applies this theorem to
the actual cover morphisms. Its reduction equality is obtained by composing
the given equality of base-changed morphisms with the original pullback's
first projection.

## Source and remaining scope

This is new native mathematics on Aglib author HEAD
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`, with Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The frozen algebraic producer
[EtaleLift.lean](../../../RingTheory/LocalRing/EtaleLift.lean) has SHA-256
`b88fe0c0a7af7d9e53e95ab0789234b0c134178a5fba6ae7adfbe5e50d7e0480`.
It was consumed without changes.

The current consumer is the residue comparison portion of
`EG-PROPER-HENSELIAN`. Fullness under a Henselian hypothesis, the resulting
category equivalence, and the proper curve comparison remain open obligations.
The production compilation covers this source and enabled compiler diagnostics;
it makes no separate lint, test, kernel replay, release or established-status
claim.
