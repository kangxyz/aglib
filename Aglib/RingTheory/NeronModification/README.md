# Affine Néron modifications

[`Basic`](Basic.lean) constructs the actual quotient imposing `p * Zᵢ = gᵢ`, then quotients
by the kernel of localization away from `p`. The resulting image of `p` is
regular. A map to a ring where the image of `p` is regular, together with
specified divisibility witnesses, factors uniquely through this construction
and preserves the original coefficients and the specified coordinates.
The index type is arbitrary and the original `p` need not be regular.

[`Lift`](Lift.lean) expresses this universal property as an algebra
homomorphism. Its uniqueness theorem retains regularity of the image of `p`
in the target.

[`BaseChange`](BaseChange.lean) constructs an algebra equivalence between a
flat scalar extension of the modification and the modification of the extended
coefficients. It preserves the original coefficients and the specified divided
coordinates. Flatness supplies the regularity used to construct the inverse.

[`ChangeGenerators`](ChangeGenerators.lean) gives a comparison map from an
inclusion of the centre ideals `span ({p} ∪ range g)`, and an algebra equivalence
when these ideals are equal. The original coefficient map is preserved.

[`Localization`](Localization.lean) proves that localizing the coefficient
ring localizes the actual modification at the images of the old scalars.
The algebra structure is induced by the constructed comparison map.

[Away](Away.lean), [Domain](Domain.lean) and [FractionField](FractionField.lean)
compare the actual modification with the original away localization and
fraction field. A nonzero distinguished element in a domain preserves the
domain, and an injective point remains injective under the prescribed lift.
[EvaluatedFittingBaseChange](EvaluatedFittingBaseChange.lean) and
[EvaluatedFittingLocalization](EvaluatedFittingLocalization.lean) transport the
evaluated differential Fitting ideals of that same modification, retaining
the original centre generators and point squares.

[OriginStep](OriginStep.lean) constructs a lifted point with strict enlargement
of any nonzero proper evaluated Fitting ideal at a translated rational centre.
[GeneralCentreStep](GeneralCentreStep.lean) proves strict enlargement at the
actual generic transcendence degree for a finite-type domain embedded in a
DVR target. It retains a local same-uniformizer DVR map, the specified generic
separably generated fraction action, residual transcendental separability,
finite source and centre generators, a proper old evaluated Fitting ideal,
and the fixed modification lift. The centre coordinates and retained minor
are derived. [GlobalPoint](GlobalPoint.lean) constructs global lifts from the
original residue-centre kernel. The
[completed-source DVR family](../DiscreteValuationRing/README.md) owns iteration
and the smooth-centre exit, and the [Henselian family](../Henselian/README.md)
owns the resulting approximation endpoints.
