# Polynomial grading and coordinate localization

`Aglib.RingTheory.MvPolynomial.Homogeneous` extends Mathlib's actual
`MvPolynomial.IsHomogeneous` predicate. `IsHomogeneous.eval₂_mul` proves
that multiplying every input variable by `c` multiplies the value of a
degree-`n` homogeneous polynomial by `c ^ n`. It permits arbitrary
commutative semirings, an arbitrary coefficient ring homomorphism and an
arbitrary variable type. No invertibility, field or finiteness assumption
is used.

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
pairing on the same lower algebraic coefficient maps. The lower owner passed
`1792099434951339000-74640`.

The lower inputs are Mathlib's polynomial, localization, monoid algebra
and grading objects. The current consumers are projective chart rings and
the actual projective twisting-sheaf section computation. These are local
algebra and coefficient comparisons; no cohomological finiteness or Serre
duality conclusion is asserted by this family.
