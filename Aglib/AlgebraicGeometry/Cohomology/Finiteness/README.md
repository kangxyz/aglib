# Proper finiteness families and exact-sequence transfer

[Modules](Modules.lean) transfers finite generation along the original
module-sheaf long exact sequence for a specified structural map from a
Noetherian ring. `moduleCohomology_finite_quotient_of_hom` takes finite
middle cohomology in degree `n` and finite kernel cohomology in degree
`n+1`, and proves finite quotient cohomology in degree `n`. The same leaf
gives middle, next-left and submodule-H⁰ transfers. Every finiteness input
uses the actual cohomology with its original structural scalar action;
no proper-finiteness input is hidden in these generic results.

[Coherent](Coherent.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent`, defines `AlgebraicGeometry.Scheme.Cohomology.ProperModuleCohomologyFinite`: for every field, every proper field scheme, every finitely presented module sheaf and every nonnegative degree, actual structural-field cohomology is finite-dimensional. This retained theorem-family interface has the proved supplier `properModuleCohomologyFinite` in [Proper/Field](../Proper/Field/README.md). Finite local bases give the actual finite-presentation witness, and H0/global-section comparison preserves the field action.

[ProperInputs](ProperInputs.lean) defines `Scheme.ProperStructureCohomologyFinite`. [StructureSheaf](StructureSheaf.lean) supplies `properStructureCohomologyFinite_of_standard`, `structureCohomology_finite_of_standard` and `structureH1_finite_of_standard`, all retaining `hstandard : ProperModuleCohomologyFinite`. The unit module's actual finite presentation and scalar-compatible cohomology comparison transfer the supplied all-module input.

[Proper/Field](../Proper/Field.lean) also proves
`properStructureCohomologyFinite` without a theorem-family premise.
Parameterized consumers can receive these proved suppliers; their retained
parameters are not unresolved mathematical assumptions of the suppliers.

[Constants](Constants.lean) separately defines `Scheme.ProperGeometricallyIntegralConstants`, retaining properness and geometric integrality for bijectivity of the actual structural constant map. Its canonical map is defined below in [Modules/Constants](../Modules/Constants.lean). No unconditional supplier of this input is claimed.

[ExactSequences](ExactSequences.lean) gives finite-middle and finite-left-successor transfer from actual long exactness. `moduleCohomology_finite_left_succ` requires finite quotient degree `n` and finite middle degree `n+1`; `moduleH0H1_finite_iff` requires finite quotient H0/H1 and equates simultaneous H0/H1 finiteness for the first and middle sheaves. These conditional transfers are independent of proper finiteness and contain no unstated H2 vanishing.

The consumers are general global-section/structure finiteness and [Euler/dimension consequences](../Exact/README.md). [Noetherian topological-dimension vanishing](../Vanishing/README.md) has a separate definition/endpoint and no proper-finiteness dependency.
