# Module and underlying abelian cohomology

| Source | Interface |
| --- | --- |
| [Acyclic](Acyclic.lean), [InjectiveAcyclic](InjectiveAcyclic.lean) and [InjectiveAcyclicSlice](InjectiveAcyclicSlice.lean) | Actual injective module sheaves are acyclic for original abelian sheaf cohomology, on the site and its actual slices. The proof does not assume scalar forgetting preserves injectives. |
| [Comparison](Comparison.lean), [DerivedExt](DerivedExt.lean) and [DerivedGamma](DerivedGamma.lean) | Original module-Ext/abelian-`Sheaf.H` comparisons in every degree and actual module evaluation `rightDerived` comparison. |
| [DerivedScalarSections](DerivedScalarSections.lean), [DerivedSlice](DerivedSlice.lean), [Restriction](Restriction.lean) | Original scalar restriction and slice maps, including the actual `restrictScalars` on coefficient-valued sections. |
| [DerivedBoundary](DerivedBoundary.lean), [ExtBoundary](ExtBoundary.lean) | Additive Gamma long exact sequence with boundary normalized through the original short-exact-sequence Ext class. |
| [Etale](Etale.lean) | Concrete small-etale module and abelian entries with the required existence and universe hypotheses discharged. |

The constant-ring action comes from the constant-sheaf adjunction unit; it does
not identify a constant ring with all global ring sections. The boundary is
additive: this interface does not assert a separately chosen native
right-derived long-exact-sequence boundary or module-linearity of the long exact
sequence. Concrete consumers are in
[EtaleCohomology](../../../../AlgebraicGeometry/EtaleCohomology/README.md).
