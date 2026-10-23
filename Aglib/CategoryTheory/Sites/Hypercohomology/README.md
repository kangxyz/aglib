# Free-representable hypercohomology

[Basic](Basic.lean) provides the generic free-representable hypercohomology
supplier, while [SheafComparison](SheafComparison.lean) identifies the
appropriate degree-zero placement with ordinary sheaf cohomology using the
actual derived-Hom/Ext comparison and retains the degree-zero section formula.
The original provider is reusable at larger coefficient universes; the
ordinary comparison applies when coefficient and site-Hom universes agree.

The current site-slice consumer is
[SheafCohomology/Slice/FreeRepresentable](../SheafCohomology/Slice/FreeRepresentable.lean).
