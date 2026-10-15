# Canonical field and relative base change

[Field](Field.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field`, constructs `Scheme.Cohomology.structureCohomologyBaseChangeMap` from actual semilinear geometric pullback. Its source is the field-tensor extension of the original structure-cohomology module, and its target is cohomology of the actual base-changed field scheme. The pure-tensor formula records the constructed map.

[Affine](Affine.lean) proves H0 normalization and the actual affine section-tensor comparison. [GlobalSections](GlobalSections.lean) uses finite affine covers, literal restriction/difference maps and exact scalar extension. [CechComparison](CechComparison.lean) identifies the field-linear/geometric Cech comparison with the original tensor map, using the actual native resolution/Ext maps and the same structural action.

[QuasiCompactSeparated](QuasiCompactSeparated.lean) supplies bijectivity of that original map in every degree for quasi-compact separated field schemes, hence for proper field schemes. No finite generation of cohomology is assumed. `properStructureCohomologyBaseChange` supplies the original predicate on this same constructed map.

[Relative](Relative.lean) allows arbitrary base schemes. `relativeEvaluation` is the actual counit; `fibreCohomology` is original cohomology of the pulled-back module. The evaluation/base-change square identifies the actual adjunction mate. `LocalFreeCohomologyBaseChange` remains explicit: proper, locally finitely presented, flat `f`; locally free/finitely presented coefficients; every geometric fibre concentrated in degree zero of rank `r`; then direct image has rank `r` and its canonical mate is invertible after every base change.

Focused imports follow these six leaves. Lower actual [module-base-change maps](../../Modules/BaseChange/README.md), structural pullback and canonical Cech/Ext comparisons supply the route. Arbitrary-base relative maps do not replace the field hypotheses of field-linear theorems.

[Flat](Flat.lean) constructs `Scheme.Modules.derivedFlatBaseChangeMap` on an actual cartesian square with the specified flat base map. [GodementUnit](GodementUnit.lean) compares that map with the bounded-below Godement construction under the actual `IsPullback`, `Flat j` and `Flat a` hypotheses. Its original-unit equation identifies the map; `isIso_baseChangeSourceUnit_of_flasque` additionally retains termwise flasqueness. These are constructed comparison/unit statements, not an unconditional base-change isomorphism for arbitrary coefficients and morphisms.
