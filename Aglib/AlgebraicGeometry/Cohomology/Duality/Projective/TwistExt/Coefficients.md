# Arbitrary coefficient twist Ext: precise model dependency

Source: [Coefficients.lean](Coefficients.lean).

The source imports the original TwistCohomology coefficient Model leaf,
using `twistingSheafTensorCoefficients` and
`twistingTensorCohomology_subsingleton_of_neg_le_degree`. Its own original
Ext/cohomology comparisons, scalar action and coefficient naturality proofs
remain byte-for-byte unchanged. The commutative base ring and coefficient
module remain arbitrary, with all original universes and hypotheses.

The former complete Coefficients facade additionally reexports derived-model
naturality and section equations. This owner does not use those declarations.
Its coefficient naturality is its own original Ext/cohomology naturality,
not `twistingDerivedGlobalSectionsTensorCoefficientsIso_naturality`.
The actual downstream section consumer CoefficientsTopHom now explicitly
imports Sections; no needed section isomorphism is removed.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Derived/CoefficientsCoherent](../Derived/CoefficientsCoherent.lean), [AlgebraicGeometry/Cohomology/Duality/Projective/Derived/CoefficientsTopHom](../Derived/CoefficientsTopHom.md).
