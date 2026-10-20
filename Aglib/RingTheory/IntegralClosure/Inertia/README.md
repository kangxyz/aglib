# Inertia and etaleness of integral closures

The actual carriers are `integralClosure R L`, their prime ideals, and the
native Galois automorphism groups. The inherited Krull topology and displayed
scalar towers are retained.

[Finite](Finite.lean) identifies the image of inertia under finite normal
restriction, using invariants of the actual kernel.
[Compactness](Compactness.lean) proves that residue conditions and inertia are
closed and lifts finitely satisfiable conditions.
[Absolute](Absolute.lean) supplies those finite conditions and proves
surjectivity onto the inertia of every finite Galois subextension at the
contraction of the same prime.

[Degree](Degree.lean) proves the finite-flat Galois degree and stabilizer
identity. Trivial inertia forces ramification index one and a Galois residue
extension. This derives residue separability without a perfectness or
characteristic-zero premise. Its integral-tower descent lemma also retains
arbitrary residue characteristic.

[Etale](Etale.lean) uses that degree argument to prove etaleness of the literal
DVR normalization. It passes from finite Galois fields to finite separable
fields and finite etale algebras, including products. Its absolute-inertia
criterion requires fixedness of **every** embedding of the original generic
algebra into the specified closure.
[Inseparable](Inseparable.lean) passes through the separable closure and proves
the criterion for the actual algebraic closure of an imperfect fraction field.

The distinct [Horizontal](Horizontal.lean),
[HorizontalAbsolute](HorizontalAbsolute.lean),
[HorizontalNonGalois](HorizontalNonGalois.lean),
[HorizontalAlgebra](HorizontalAlgebra.lean), and
[HorizontalModel](HorizontalModel.lean) route keeps an actual algebra structure
from a characteristic-zero field to the DVR. Characteristic zero of the DVR
alone does not provide that hypothesis. The Galois-action helpers used by the
arbitrary-residue route have their explicitly weaker statements.

[FixesPoints](FixesPoints.lean) proves the forward statement that inertia fixes
every point of an actual finite etale algebra, using native unramified
rigidity. The parent [Inertia](../Inertia.lean) defines the literal decomposition
and inertia subgroups, their continuous inclusion, integral roots of unity,
a chosen maximal prime above a DVR closed point, and the residue-action kernel
comparison. Invertibility of the root order is retained.

The native [finite normalization](../FiniteEtale.lean) provides finiteness,
freeness, flatness, product comparison, and the canonical generic-fiber map.
[Actions](../Actions.lean) supplies restriction and lifting of maps, automorphism
and monoid-action equivalences, and the same generic-fiber square. No replacement
normalization carrier is introduced.

The source cohort is R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`;
the leaves record exact source hashes. Current consumers are the finite etale
normalization and torsor extension constructions.
