# Proved proper finiteness on field schemes

[The field supplier](../Field.lean) proves the retained
`ProperModuleCohomologyFinite` and `ProperStructureCohomologyFinite`
interfaces without a theorem-family premise. It specializes the proved
Noetherian-base theorem at the field's original structural morphism.
Finite presentation supplies the native affine-chart coherence property,
and the existing scalar action agrees literally with field constants.

`moduleGlobalSections_finite_of_proper` uses the original H0 equivalence.
The original module and structure cohomology objects and actions are
preserved. Existing consumers which retain an explicit family parameter
can now receive `properModuleCohomologyFinite` directly. The independent
all-field/all-degree consumer passed, with the three standard axioms only.
