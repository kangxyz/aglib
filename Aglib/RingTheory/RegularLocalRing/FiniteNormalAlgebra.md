# Finite normal algebras over regular local surfaces

[FiniteNormalAlgebra.lean](FiniteNormalAlgebra.lean) proves finite freeness for
an actual finite injective local map `f : R →+* A`. The source is a commutative
regular local ring of dimension two. The target is a commutative Noetherian
normal local domain of dimension two. The scalar action is induced by the
same map `f`. Completeness, a coefficient field, flatness and a
Cohen--Macaulay hypothesis are not inputs.

`RingHom.Finite.free_of_normal_dimension_two` exposes the specified-map
statement. The algebra-map interfaces are
`IsRegularLocalRing.projectiveDimension_le_zero_of_finite_normal_dimension_two`,
`IsRegularLocalRing.projective_of_finite_normal_dimension_two` and
`IsRegularLocalRing.free_of_finite_normal_dimension_two`. The existing finite
module hypothesis together with the last conclusion gives finite freeness.

The proof uses an ordered regular parameter pair `(u,v)` of R. For the original
extended maximal ideal, integrality and locality give
`radical(m_R A) = m_A`. This is exposed as
`IsLocalRing.radical_map_maximalIdeal_of_isIntegral`; it expresses the fact
that the finite local closed fibre has only its closed point. Consequently
no height-one prime of A contains both `f(u)` and `f(v)`. If
`f(v) * x = f(u) * y`, height-one divisibility gives `f(u) ∣ x` in A. This
proves injectivity of multiplication by the original second parameter on
the original first-parameter quotient.

The reusable pair interfaces are
`IsIntegrallyClosed.isSMulRegular_quotient_of_pair_avoids_height_one`,
`IsIntegrallyClosed.isRegular_pair_of_radical_eq_maximalIdeal` and
`IsIntegrallyClosed.isRegular_pair_of_finite_local_algebra`. The latter
preserves the original restricted R-action and needs only the stated
source parameter pair, finite injective local algebra map, and normal
Noetherian local target of dimension at least two. A parameter pair on a
singular target need not generate its maximal ideal.

For the finite-free conclusion, the two original regular multiplication
short exact sequences increase projective dimension by two after passage
to their successive quotients. The existing regular-local dimension bound
puts the final finite quotient in projective dimension at most two.
Cancellation gives projective dimension at most zero for A over R.
Projectivity and the local finite-module freeness theorem finish the proof.
The divisibility supplier is the tracked
[HeightOneDivisibility](../IntegralClosure/HeightOneDivisibility.lean);
the earlier `MaximalIdealDual` candidate is not a dependency.

The current consumer is the regular-base canonical-module construction
`omega_A = Hom_R(A,R)`, with action `(a • lambda)(b) = lambda(b*a)`.
Finite freeness will make the existing coinduction functor exact. This
file does not construct the finite regular subring, prove general
Cohen--Macaulay concentration, identify a surface canonical module, or
establish derived biduality, trace compatibility, Grauert--Riemenschneider
vanishing or B7 boundedness. Those remain separate R.V3 and geometric
obligations.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. This is the native
implementation of Section 1 of the fixed regular-base duality route v1;
that research packet remains unchanged. Native compilation and diagnostics
are coordinated by the principal; this author retains the coupled proof
repair obligation.
