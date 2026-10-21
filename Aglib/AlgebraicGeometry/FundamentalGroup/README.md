# Etale fundamental groups

`Basic` constructs automorphisms of the actual finite-etale fibre functor in
`AlgebraicGeometry.Scheme.EtaleFundamentalGroups`. Its pointed maps retain the
chosen field-valued points, fibre identifications and section equations.
`Split` supplies the split-group interfaces used by continuous first cohomology.

The finite-stage and geometric-kernel leaves construct compatible cover models,
actions and natural automorphisms. Their explicit model, descent and comparison
inputs remain visible. `GeometricExactness` contains the qcqs/rational-section
endpoint and `stacks0BTX_actual`; the theorem types govern their precise
conditions. `SectionLifting` belongs to `Scheme.FiniteEtale.SectionLifting` and
uses the actual base-change fullness statement. Its henselian application retains
`ProperHenselianComparison R` and the original ring hypotheses.

`Field.Basic` compares the actual field fibre automorphisms with the absolute
Galois group. Its characteristic-zero identification endpoint retains
`[CharZero F]`; the earlier forward construction has its original assumptions.
The cyclotomic leaves preserve finite level, primitive-root, root-coordinate and
characteristic hypotheses at each endpoint.

[Field/ArbitraryGalois](Field/ArbitraryGalois.lean) reconstructs the actual
Galois group of an arbitrary Galois extension from natural automorphisms of its
field-valued finite-etale point functor, with the continuous comparison and
identity-coefficient H1 injection. This does not assert full faithfulness of
that functor for an arbitrary field. [Field/OverRing](Field/OverRing.lean)
compares the original generic and model coefficient actions and classes; its
actual normalization and coefficient premises are retained. The
[local class-extension family](../Normalization/InertiaTorsor/README.md)
consumes these comparisons.

Lower dependencies are the native finite-etale cover/fibre/base-change API,
finite-stage descent, generic functor automorphism transport, split groups and
continuous H1. Current consumers include finite-etale monodromy and the actual
small-etale H1 comparison family. Specialized curve and arithmetic applications
remain downstream.
