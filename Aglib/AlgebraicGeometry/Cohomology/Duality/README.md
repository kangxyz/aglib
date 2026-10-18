# Native Laurent monomial residue duality

Import `Aglib.AlgebraicGeometry.Cohomology.Duality.LaurentPairing`, or a focused
leaf below. The family `Duality/LaurentPairing/` supplies finite monomial pieces
and the original coefficient residue pairing needed for projective cohomology.
It retains the native coordinate Laurent algebra, exponent monoid, coefficient
maps and polynomial homogeneous submodule. There is no substitute quotient
cohomology object, replacement derived category, or theorem-family input.

Let `ι` be a finite coordinate type and `R` any commutative ring. The residue
exponent is the existing `coordinateNegativeProductExponent Finset.univ`, whose
coordinates are all `-1` and whose degree is `-Fintype.card ι`.

## Exponents and finite free pieces

[Exponents](LaurentPairing/Exponents.lean) is a compatibility import of the sole
algebraic implementation in
[`RingTheory/MvPolynomial/CoordinateExponents`](../../../RingTheory/MvPolynomial/CoordinateExponents.lean).
It works in the original
`MvPolynomial.coordinateExponentMonoid Finset.univ`:

- `coordinateNegativeComplement a` is literally `βᵢ = -1 - αᵢ`, for an original
  natural exponent `a : ι →₀ ℕ`; `coordinateNonnegativeComplement` is its inverse
  on all-negative Laurent exponents.
- `coordinateNegativeComplementEquiv` identifies those actual exponent types.
  `coordinateNegativeComplement_degree` proves degree `-a.degree - card ι`.
- `coordinateNegativeDegreeExponents d` is the native exponent subtype with
  degree `d` and every coordinate negative. `coordinateNegativeDegreeExponentEquiv`
  identifies it with natural exponents of integer degree `-d - card ι`.
- This subtype is finite for every integer `d`, using Mathlib's finite
  natural-exponent degree theorem. `coordinateNegativeDegreeExponents_isEmpty`
  proves emptiness when `-card ι < d`.

[Pieces](LaurentPairing/Pieces.lean) is a compatibility import of the sole
algebraic implementation in
[`RingTheory/MvPolynomial/CoordinatePieces`](../../../RingTheory/MvPolynomial/CoordinatePieces.lean).
The original native submodules and all declaration names are unchanged:

- `coordinateNegativePiece R d` is exactly
  `AddMonoidAlgebra.supported R R {e | coordinateDegree univ e = d ∧ ∀ i, e.val i < 0}`.
- `coordinateNegativePieceEquivFinsupp` is the native supported-coefficient
  equivalence; its application is the original Laurent coefficient at the
  displayed exponent.
- `homogeneousPieceEquivFinsupp` uses the original
  `MvPolynomial.homogeneousSubmodule ι R m`, and retains original polynomial coefficients.
- `coordinateNegativePieceBasis` and `homogeneousPieceBasis` are native bases;
  their values are the original Laurent single monomials and polynomial monomials.
  The negative pieces are finite free. Polynomial homogeneous pieces are free
  for arbitrary coordinate types and finite when the coordinate type is finite.
- `coordinateHomogeneousNegativeExponentEquiv m` identifies polynomial degree
  `m` with all-negative Laurent degree `-(m : ℤ) - card ι`, by the same literal
  exponent complement. `coordinateExponentOfNat_add_negativeComplement` states
  that the original two exponents sum to the existing residue exponent.
- `coordinateNegativePiece_eq_bot` proves the original negative submodule is
  zero above residue degree.

Ring and coordinate universes are independent. No Noetherian, field,
nontrivial-ring, or geometric finiteness premise is used.

## The original residue coefficient pairing

[Pairing](LaurentPairing/Pairing.lean) defines `coordinateLaurentResiduePairing R m`
between the original polynomial degree-`m` piece and the actual negative piece
in degree `-m - card ι`. Its value is exactly

```text
((toCoordinateLaurent R univ p.val) * g.val).coeff
  (coordinateNegativeProductExponent univ)
```

`coordinateLaurentResiduePairing_basis` identifies the original basis pairing
with the Kronecker symbol for complementary exponents. The native
`LinearMap.IsPerfPair` assertion therefore retains bijectivity of both maps to
linear duals. `coordinateLaurentResidueDuality` is the native `toPerfPair`
equivalence, whose application is the same literal coefficient of the product.
The opposite duality is the native `coordinateLaurentResiduePairing.flip.toPerfPair`.

This is an algebraic monomial duality.
[Projective/MonomialTrace](Projective/MonomialTrace.lean) identifies it
with the original geometric pairing through the actual monomial/Cech and
`Sheaf.H` comparisons; [TwistDuality](Projective/TwistDuality.lean) proves
perfectness of that same twist pairing. The independent
`Algebra.Homology.Simplex.Relative.Trace` result already fixes the top
full-support tuple class by evaluation on the increasing identity tuple.
No general proper cohomology model or arbitrary-base local-freeness family
is discharged by the monomial calculation alone.

## Validation

Each source leaf is checked individually by the shared serialized wrapper:

| Leaf | Successful receipt |
| --- | --- |
| Exponents | `1792080025170350000-39282` |
| Sole lower coordinate-exponent owner, including nonnegative degree fibers | `1792085028459247000-10220` |
| Exponents compatibility import | `1792085060922228000-10858` |
| Pieces | `1792080223589632000-42702` |
| Pairing | `1792080508834548000-46356` |
| Family entry, including refresh after the lower grading extension | `1792080765733325000-50017` |

The external task consumer `work/proper-validation/LaurentPairingConsumer.lean`
passed with receipt `1792080826265772000-50650`. It checks independent ring and
coordinate universes, negative-exponent finiteness, native finite/free instances,
both native duality directions, the literal product coefficient formula,
vanishing above residue degree, and the minimal polynomial-coordinate hypotheses.
The exponent equivalence, negative-piece vanishing, native perfect-pairing proof
and duality equivalence depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The original consumer was refreshed after the lower-owner extraction, receipt
`1792085145941296000-12513`, with the same declarations, statements and standard axioms.
