# Schematic degree of positive-level multiplication

[MultiplicationFiniteDegree.lean](MultiplicationFiniteDegree.lean) proves the
following properties of the literal morphism `(𝟙 G.X) ^ n` for an actual
group object `G : Grp (FScheme k)` over an arbitrary field:

- `multiplication_ne_one_of_pos`: it differs from the constant origin map;
- `multiplication_finite_flat_surjective_of_pos`: it is finite, flat, and surjective;
- `multiplication_nativeRank_of_pos`: its native `Scheme.Hom.finrank` equals
  `n * n` at every actual target point;
- `multiplication_hasLocallyFreeRank_of_pos`: its actual direct-image structure
  sheaf has locally free rank `n * n`;
- `multiplication_finite_flat_degree`: the finite, flat, surjective, and locally
  free rank conclusions together.

Each endpoint assumes `hG : Curve.Properties G.X`, the explicit hypothesis
`Curve.coherentGenus k G.X = 1`, and `0 < n`. Invertibility of `n`, characteristic
zero, etaleness, separability, and a degree or basis family are not required.
These conclusions apply to the existing literal multiplication-kernel
construction, including its finite kernels at inseparable levels.

Over an algebraically closed field, the proved
`pullback_twice_identityIdealClass` identifies the pullback of twice the identity
ideal class with its `n * n` multiple. That class has degree `-2`, while its
pullback by the constant origin map is zero. Positivity of `n` therefore rules
out the constant map. Base change to the algebraic closure, preservation of the
actual multiplication map, and coherent-genus base change give the same
nonconstancy over the original field. The existing pointed nonconstant curve-map
theorem supplies finiteness and surjectivity.

`Curve.dominant_flat` supplies the needed flatness on the original morphism.
Its proof identifies every target stalk as a field or a DVR and proves
injectivity of the actual stalk map through the compatible function-field map.
The source stalk is consequently torsion-free over that Dedekind domain and
hence flat. This auxiliary theorem applies to dominant maps between the same
native smooth-curve objects.

Finite flatness and finite presentation give actual local free bases. The native
curve-degree pullback theorem compares their constant rank with the square
formula, forcing rank `n * n` over an algebraically closed field. Native rank
compatibility in the actual base-change square then proves the rank statement
at every point over the original arbitrary field. The all-field locally free
rank statement follows from the existing comparison with native rank.

These ranks include nonreduced fibre multiplicities. This file does not assert
`HasGeometricDegree` with value `n * n` at a noninvertible level: that predicate
counts geometric points. The existing invertible-level theorem in
[MultiplicationDegree.lean](MultiplicationDegree.lean) retains its separate unit
hypothesis and etaleness conclusion.

The geometric inputs are proved in [MultiplicationDegree.lean](MultiplicationDegree.lean)
and [PointDivisor.lean](PointDivisor.lean). The generic finite-map, genus-base-change,
local-freeness and degree-comparison arguments use their native proved suppliers.
All conclusions concern the original group, curve and multiplication map.
