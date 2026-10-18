# Euler characteristics of original fibre complexes

[Fiber](Fiber.lean), imported as
`Aglib.Algebra.Homology.EulerCharacteristic.Fiber`, proves
`CochainComplex.isLocallyConstant_eulerChar_residueField` and
`isLocallyConstant_homologyEulerChar_residueField`. For a termwise bounded
integer complex of finitely presented flat modules, the termwise and
homological Euler characteristics of the original residue-field
scalar-extension complex are locally constant on `PrimeSpectrum R`.
The finite-projective specialization is
`isLocallyConstant_homologyEulerChar_residueField_of_projective`.

The proof uses the original interval of term bounds, the native alternating
signs and finite sum, and
`ModuleCat.extendScalarsAlgebraObjIso` on each unchanged term. The native
Euler–Poincare identity in [the parent leaf](../EulerCharacteristic.lean)
identifies the actual homological and termwise Euler characteristics after
every residue-field extension. The ring need not be Noetherian or nonzero;
global freeness and homology/tensor compatibility are not premises.

The focused leaf and an external public consumer passed the serialized
single-target build workflow. The consumer includes independent ring and
module universes, both the finitely presented flat and finite-projective
interfaces, and the native `HomologicalComplex.homologyEulerChar`.
Axiom inspection reports only `propext`, `Classical.choice` and `Quot.sound`.
No aggregate library build was run.

[Cohomology](Cohomology.lean) works over a nontrivial ring and proves the native
homological rank-support and finite-sum formulas under cohomological bounds,
without strict term bounds or finite terms. In particular,
`CochainComplex.homologyEulerChar_eq_sum_range` identifies the existing
integer-indexed Euler characteristic with the usual alternating sum of
the original homology dimensions in degrees `0` through `n`. It neither
requires finite terms nor replaces the native homology object. This leaf
passed `1792101994033089000-20341` under the default budgets and linters.
