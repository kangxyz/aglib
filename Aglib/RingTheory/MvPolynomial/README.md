# Polynomial grading and coordinate localization

`Aglib.RingTheory.MvPolynomial.Homogeneous` extends Mathlib's actual
`MvPolynomial.IsHomogeneous` predicate. `IsHomogeneous.eval₂_mul` proves
that multiplying every input variable by `c` multiplies the value of a
degree-`n` homogeneous polynomial by `c ^ n`. It permits arbitrary
commutative semirings, an arbitrary coefficient ring homomorphism and an
arbitrary variable type. No invertibility, field or finiteness assumption
is used. `MvPolynomial.finrank_homogeneousSubmodule_le` bounds the dimension of
the degree-`m` homogeneous polynomials in finitely many variables `σ` over a field
by `(m + 1)^{|σ|}`, counting the monomials of degree `m`; Mumford's bound uses it for
`h⁰(O(m))`.

`Aglib.RingTheory.MvPolynomial.GradedMap` bundles the original
`MvPolynomial.map f` as `gradedMap f` for the actual total-degree grading,
with native identity and composition equations. It works for commutative
semirings with independent coefficient and variable universes. For
commutative rings, `irrelevant_map_gradedMap` proves that the original
irrelevant ideal maps onto the new irrelevant ideal. The existing
`irrelevant_homogeneousSubmodule_eq_idealOfVars` declaration is owned here;
its original proof was moved from `ProjectiveSpace.Basic`, which now imports
this sole implementation. Its ring and variable universes are independent.
The actual projective-space coefficient map and base-change charts consume
these lower normalizations.

The immediate consumer is the projective chart calculation: evaluating
homogeneous coordinates at the fractions `Xⱼ / Xᵢ` divides a homogeneous
polynomial of degree `n` by `Xᵢ ^ n`.

`Aglib.RingTheory.MvPolynomial.CoordinateLocalization` uses the native
additive monoid algebra on finitely supported integer exponent vectors
which are nonnegative outside a finite coordinate set `s`. The original
polynomial map casts each exponent to an integer and retains every
coefficient. Explicit common-denominator clearing proves that this algebra
is a localization away from `∏ i ∈ s, Xᵢ`. `coordinateLocalizationEquiv`
identifies it with the actual `Localization.Away` as an algebra over `R`.
The displayed fraction formula and the coefficient/exponent-preserving
maps for `s ⊆ t`, including identity and composition, are proved. The
coordinate type may be infinite, and `R` is any commutative ring.

`Aglib.RingTheory.MvPolynomial.CoordinateGrading` uses Mathlib's native
`AddMonoidAlgebra.gradeBy` with `Finsupp.degree`. Its degree pieces have the
original monomial `Finsupp` coordinates. Polynomial homogeneity is
preserved and reflected, and a homogeneous fraction has degree equal to
numerator degree minus denominator degree. The actual
`HomogeneousLocalization.Away` is identified with the degree-zero Laurent
ring, retaining `fromZeroRingHom` on coefficients. For an inverted
coordinate `i ∈ s`, `coordinateGradeShift` identifies degree zero with any
integer degree by multiplication by the actual monomial `Xᵢ^d`, with
inverse `Xᵢ^(-d)`. The original inclusion maps preserve every degree.
`coordinateVariableUnit` is the native Laurent unit of an inverted
coordinate. Its arbitrary integer powers have exactly the corresponding
one-coordinate exponents, and `toCoordinateLaurent_X` preserves the original
polynomial variable.

`Aglib.RingTheory.MvPolynomial.CoordinateExponents` owns the integer
monomial index calculations. The literal complement `βᵢ = -1 - αᵢ`
identifies natural polynomial exponents with all-negative Laurent
exponents and preserves the exact degree equation. Fixed-degree
nonnegative and all-negative exponent types are finite for finite
coordinate types, and their respective degree bounds give emptiness.
The former `Cohomology.Duality.LaurentPairing.Exponents` leaf delegates
to this sole algebraic implementation with unchanged declaration names.

`Aglib.RingTheory.MvPolynomial.CoordinatePieces` is the sole implementation
of the original homogeneous polynomial pieces and supported all-negative
Laurent pieces, with native coefficient-preserving Finsupp equivalences,
explicit monomial bases, finite/free results and negative-piece vanishing.
It was extracted from `Cohomology.Duality.LaurentPairing.Pieces` without
changing declarations or proofs; the old leaf is a compatibility import.
This keeps the original projective global-section computation and residue
pairing on the same lower algebraic coefficient maps.

[DegreeOne](DegreeOne.lean) supplies the original coordinate basis
`homogeneousDegreeOneBasis` of the actual `homogeneousSubmodule ι R 1`.
Its native basis coordinates are exactly `coeff (Finsupp.single i 1)`,
and `degreeOneExponentEquiv` identifies coordinate indices with the original
degree-one monomial exponents. The coordinate type is arbitrary, ring and
index universes are independent, and a commutative semiring suffices,
including the singleton semiring. No finite, field, domain, nontrivial,
or Noetherian premise is added.

The lower inputs are Mathlib's polynomial, localization, monoid algebra
and grading objects. The current consumers are projective chart rings and
the actual projective twisting-sheaf section computation. These are local
algebra and coefficient comparisons; no cohomological finiteness or Serre
duality conclusion is asserted by this family.

## Scaled expansion and quadratic remainders

[ScaledTaylor](ScaledTaylor.lean) proves
`MvPolynomial.exists_scaled_firstOrder_remainder` in finitely many variables over arbitrary commutative
coefficient algebras: increments in an ideal have a remainder in its square,
with the square of the chosen scale retained as an explicit factor.
[QuadraticRemainder](QuadraticRemainder.lean) identifies the vanishing value and
first derivatives at the origin of such quadratic remainders.
[AdjugateExpansion](AdjugateExpansion.lean) applies this identity to a finite
square system and the adjugate of its actual evaluated partial-derivative matrix.

These providers allow empty variable types, zero scales, and zero divisors.
They neither require nor assert a Henselian or approximation property. The
Henselian consumer is `Aglib.RingTheory.Henselian.DeterminantCorrection`.

[AffineScaling](AffineScaling.lean) gives the derivative chain rule for
simultaneous affine scaling over arbitrary commutative rings. Its divided
relation formula cancels the scale only after evaluation in a target where
that scale is regular. [LocalConstantDivisibility](LocalConstantDivisibility.lean)
recovers divisibility of the constant from an actual local point when the
linear coefficients and the scaled remainder vanish modulo a generator of
the source maximal ideal; this step needs neither separability nor regularity
of that generator. The rational-centre Néron step uses these formulas.

[ResidueFrobenius](ResidueFrobenius.lean) proves independence of finite
coefficient-times-monomial families over the literal rational Frobenius range,
with distinct exponent vectors bounded by the characteristic.
[RationalFrobenius](RationalFrobenius.lean) clears actual fraction denominators
to turn the supplied finite monomial-independence condition into geometric
reducedness. [CoefficientFractionFrobenius](CoefficientFractionFrobenius.lean)
supplies the rational coefficient-extension result from geometrically reduced
field coefficients in prime characteristic. All scalar towers and polynomial
maps remain explicit; no finite imperfection degree or finite variable type
is required. The parameter-DVR completion argument consumes these results.
