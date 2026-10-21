# Henselian local rings and polynomial approximation

`Quadratic` constructs `HenselianLocalRing.of_isAdicComplete` from actual
maximal-ideal adic completeness. Its quadratic-root theorem uses a unit linear
coefficient and a constant coefficient in the maximal ideal; it produces a
root in that ideal without inverting the leading coefficient.

The same leaf proves `IsLocalRing.isUnit_add_of_mem_maximalIdeal`, which
requires locality, a unit and a maximal-ideal summand. The general completion
and finite-target lifting providers remain in the existing completion and
smooth families.

[Finite-algebra idempotents](FiniteAlgebraIdempotents.md) lifts each prescribed
idempotent modulo the extended maximal ideal in any finite commutative algebra
over a Henselian local ring. It retains the actual quotient map and requires
no Noetherianity, flatness, étaleness or completeness.

## Polynomial systems and étale points

[PolynomialSystem](PolynomialSystem.lean) lifts a solution of a finite square
system modulo any proper ideal of a Henselian local ring when the evaluated
Jacobian determinant is a unit. The exact solution retains the original
quotient coordinates; neither Noetherianity nor finite generation of the ideal
is required.
[DeterminantCorrection](DeterminantCorrection.lean) supplies
`HenselianLocalRing.exists_eval_eq_zero_of_mem_det_sq_mul`: if the error lies
coordinatewise in `Ideal.span {δ ^ 2} * a`, for a proper ideal `a` and the
evaluated Jacobian determinant `δ`, an exact solution has differences in
`Ideal.span {δ} * a`. The determinant may be zero or a zero divisor. The proof
uses the adjugate-scaled expansion without cancelling `δ ^ 2`; its matrix has
equations in rows and variables in columns.

[Etale](Etale.lean) gives `HenselianLocalRing.residue_comp_bijective_of_etale`,
unique lifting of points of an arbitrary étale algebra from the residue field.
[EtaleQuotientLifting](EtaleQuotientLifting.lean) gives
`HenselianLocalRing.quotient_comp_bijective_of_etale` for every proper ideal
`I`, using literal composition with `Ideal.Quotient.mkₐ R I`.
It combines residue lifting with [local-target uniqueness](../Etale/LocalPoints.lean)
on `R ⧸ I`; it requires no nilpotence, finite-generation, Noetherianity or
completeness assumption.

## Henselization and polynomial-origin approximation

[EtaleNeighborhood](EtaleNeighborhood.lean) defines the small filtered category
`PointedEtaleNeighborhood R` of pointed étale neighborhoods of a commutative
local ring, using native `FGAlgCatSkeleton R` presentations and maps preserving
the actual residue point. Tensor-product successors and one-element
localizations give the filtering maps. The category and its diagram use the
base ring's universe; `exists_equiv` also transports étale presentations from
independent universes. [Henselization](Henselization.lean) takes the native
colimit, with its local, Henselian and universal-property interfaces in
[HenselizationLocalRing](HenselizationLocalRing.lean),
[HenselizationHenselian](HenselizationHenselian.lean) and
[HenselizationUniversal](HenselizationUniversal.lean).

For an arbitrary field `k` and `n : ℕ`, [PolynomialLocalRing](PolynomialLocalRing.lean)
is the localization of `MvPolynomial (Fin n) k` at the origin, and
[PolynomialLocalHenselization](PolynomialLocalHenselization.lean) is its actual
Henselization `H`. In
[PolynomialLocalHenselizationIdealApproximation](PolynomialLocalHenselizationIdealApproximation.lean),
`PolynomialLocalHenselization.exists_solution_ideal_completion_with_precision`
takes a finite polynomial system over `H`, a solution in the native
`AdicCompletion I H` for any proper ideal `I`, and any `c : ℕ`. It returns an
exact solution in the original `H`, with equality under the original quotient
projection modulo `I ^ c` and error in the extended ideal `I ^ c` of that
same completion.

[PolynomialLocalHenselizationFiniteLocalApproximation](PolynomialLocalHenselizationFiniteLocalApproximation.lean)
gives `PolynomialLocalHenselization.exists_solution_finite_local_ideal_completion_with_precision`
for every finite commutative local `H`-algebra `A` and every proper ideal
`J : Ideal A`. It returns an exact solution in the original `A`, with the
original quotient-projection equality and extended-ideal precision modulo `J ^ c`.
Here `k` and `A` share one universe; the finite variable and equation types have
independent universes. The statement derives locality of the structural map
and the needed cofinality comparison. It requires no caller-supplied solver,
cofinality bound, flatness or free-module structure on `A`. The full excellent-DVR and
general geometric-local Artin statements remain open extensions of this scope.
