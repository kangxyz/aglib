# Explicit proper finiteness and exact-sequence transfer

[Coherent](Coherent.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent`, defines `AlgebraicGeometry.Scheme.Cohomology.ProperModuleCohomologyFinite`: for every field, every proper field scheme, every finitely presented module sheaf and every nonnegative degree, actual structural-field cohomology is finite-dimensional. This is an explicit retained input. Finite local bases give the actual finite-presentation witness, and H0/global-section comparison preserves the field action.

[ProperInputs](ProperInputs.lean) defines `Scheme.ProperStructureCohomologyFinite`. [StructureSheaf](StructureSheaf.lean) supplies `properStructureCohomologyFinite_of_standard`, `structureCohomology_finite_of_standard` and `structureH1_finite_of_standard`, all retaining `hstandard : ProperModuleCohomologyFinite`. The unit module's actual finite presentation and scalar-compatible cohomology comparison transfer the supplied all-module input.

[Constants](Constants.lean) separately defines `Scheme.ProperGeometricallyIntegralConstants`, retaining properness and geometric integrality for bijectivity of the actual structural constant map. Its canonical map is defined below in [Modules/Constants](../Modules/Constants.lean). No unconditional supplier of this input is claimed.

[ExactSequences](ExactSequences.lean) gives finite-middle and finite-left-successor transfer from actual long exactness. `moduleCohomology_finite_left_succ` requires finite quotient degree `n` and finite middle degree `n+1`; `moduleH0H1_finite_iff` requires finite quotient H0/H1 and equates simultaneous H0/H1 finiteness for the first and middle sheaves. These conditional transfers are independent of proper finiteness and contain no unstated H2 vanishing.

The consumers are general global-section/structure finiteness and [Euler/dimension consequences](../Exact/README.md). [Noetherian topological-dimension vanishing](../Vanishing/README.md) has a separate definition/endpoint and no proper-finiteness dependency.
