# Finite etale residue lifts

The implementation is [EtaleLift.lean](EtaleLift.lean). Its current consumer is
the residue essential-surjectivity obligation in the finite-etale part of
`EG-PROPER-HENSELIAN`.

## Interfaces and assumptions

Let `R : Type u` be a commutative local ring and let
`k = IsLocalRing.ResidueField R`, with its native `R`-algebra structure.

- `IsLocalRing.exists_monic_separable_residue_lift` takes an actual field
  `L : Type v` with `[Algebra k L]`, `[FiniteDimensional k L]` and
  `[Algebra.IsSeparable k L]`. It supplies a monic separable `f : R[X]` and an
  actual `k`-algebra equivalence `k ⊗[R] AdjoinRoot f ≃ₐ[k] L`.
- `IsLocalRing.exists_finite_etale_residue_lift` gives the resulting algebra
  `A : Type u`, its commutative ring and `R`-algebra structures, proofs of
  `Module.Finite R A` and `Algebra.Etale R A`, and the same residue equivalence.
- `IsLocalRing.exists_finite_etale_residue_lift_of_etale` takes any actual
  commutative `k`-algebra `B : Type v` with `[Algebra.Etale k B]`. It supplies
  `A : Type (max u v)` with the same finite-etale properties and
  `k ⊗[R] A ≃ₐ[k] B`. The pinned field-decomposition theorem already implies
  that `B` is finite over `k`; no extra finiteness assumption is needed.

These results retain independent universes and require no Henselian,
Noetherian or excellent hypothesis. The general endpoint includes the zero
algebra through the empty finite product.

## Construction and maps

For a finite separable field extension, choose the native primitive-element
power basis and lift its monic minimal polynomial along the surjective map
`IsLocalRing.residue R`. The lemma
`IsLocalRing.isCoprime_of_monic_of_residue` shows that coprimality with a monic
polynomial lifts: the resultant reduces to a nonzero residue-field resultant,
so it is a unit in `R`. Its proof accounts for possible degree drop of the
second polynomial. Applying this to the derivative proves separability of the
lifted polynomial.

`AdjoinRoot.etale_of_monic_of_separable` identifies the root algebra with the
native standard-etale algebra for the pair `(f, 1)`. Monicity supplies module
finiteness. `AdjoinRoot.baseChangeEquiv` combines Mathlib's `tensorAlgEquiv`
with `Algebra.TensorProduct.rid`; its scalar map is exactly `algebraMap R k`,
which is `IsLocalRing.residue R`. The proved `baseChangeEquiv_root` equation
sends `1 ⊗ₜ AdjoinRoot.root f` to the root of the residue polynomial. The
primitive-element equivalence then identifies this fibre with the supplied
field `L`.

For `B`, the construction uses
`Algebra.Etale.iff_exists_algEquiv_prod` to obtain an actual algebra equivalence
with a finite product of finite separable fields. It lifts each factor and
composes `Algebra.TensorProduct.piRight`, the product of the constructed fibre
equivalences, and the inverse of the supplied decomposition equivalence.

## Source and evidence boundary

This is new native Aglib mathematics in the author checkout based at
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`, using Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The source imports precise Mathlib
leaves and has no dependency on the existing Henselian lifting modules.

The changed production module compiled successfully with the assigned guarded
serial build in `residue_etale_lift/build-005` under the investigation scratch
directory. This is fresh module compilation with enabled compiler diagnostics;
it does not assert separate lint, test, kernel replay or release coverage.

The supplied construction proves object lifting. Full faithfulness of residue
base change, a bundled finite-etale category equivalence, and the proper curve
comparison remain separate obligations. No established exposé status is assigned
by this module or its build result.
