# Canonical field and relative base change

[Field](Field.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field`, constructs `Scheme.Cohomology.structureCohomologyBaseChangeMap` from actual semilinear geometric pullback. Its source is the field-tensor extension of the original structure-cohomology module, and its target is cohomology of the actual base-changed field scheme. The pure-tensor formula records the constructed map.

[Affine](Affine.lean) proves H0 normalization and the actual affine section-tensor comparison. [GlobalSections](GlobalSections.lean) uses finite affine covers, literal restriction/difference maps and exact scalar extension. [CechComparison](CechComparison.lean) identifies the field-linear/geometric Cech comparison with the original tensor map, using the actual native resolution/Ext maps and the same structural action.

[QuasiCompactSeparated](QuasiCompactSeparated.lean) supplies bijectivity of that original map in every degree for quasi-compact separated field schemes, hence for proper field schemes. No finite generation of cohomology is assumed. `properStructureCohomologyBaseChange` supplies the original predicate on this same constructed map.

[Relative](Relative.lean) allows arbitrary base schemes. `relativeEvaluation` is the actual counit; `fibreCohomology` is original cohomology of the pulled-back module. The evaluation/base-change square identifies the actual adjunction mate. `LocalFreeCohomologyBaseChange` remains explicit: proper, locally finitely presented, flat `f`; locally free/finitely presented coefficients; every geometric fibre concentrated in degree zero of rank `r`; then direct image has rank `r` and its canonical mate is invertible after every base change.

Focused imports follow these leaves. Lower actual [module-base-change maps](../../Modules/BaseChange/README.md), structural pullback and canonical Cech/Ext comparisons supply the route. Arbitrary-base relative maps do not replace the field hypotheses of field-linear theorems.

The general [module-coefficient family](Modules/README.md) works over arbitrary
commutative structural rings. [Modules/Separated](Modules/Separated.lean)
proves canonical flat base change in every nonnegative degree for a
quasi-compact separated morphism to `Spec A` and arbitrary quasicoherent
coefficients. It identifies the actual tensor mate and its geometric unit
formula. [Modules/Qcqs](Modules/Qcqs.lean) extends the original canonical
map to quasi-compact quasi-separated `f`, in every degree and for an
arbitrary supplied Cartesian square over `A → B`. Its compact-open
induction uses actual open-restriction and Mayer–Vietoris comparisons.
No field, Noetherianity or finiteness premise is needed. The
[derived comparison](Derived/README.md) is proved over arbitrary bases
for qcqs `f`, flat base change and D+ objects with quasicoherent original
homology. The higher-direct-image specialization is recorded below.

[Flat](Flat.lean) constructs `Scheme.Modules.derivedFlatBaseChangeMap` on an actual cartesian square with the specified flat base map. [GodementUnit](GodementUnit.lean) compares that map with the bounded-below Godement construction under the actual `IsPullback`, `Flat j` and `Flat a` hypotheses. Its original-unit equation identifies the map; `isIso_baseChangeSourceUnit_of_flasque` additionally retains termwise flasqueness. These are constructed comparison/unit statements, not an unconditional base-change isomorphism for arbitrary coefficients and morphisms.

[HigherDirectImage](HigherDirectImage.lean) gives the actual natural map
`R^n f_* ; j* → a* ; R^n b_*` as homology of the original installed derived
flat comparison through the native single and exact-pullback isomorphisms.
Its component equation, coefficient naturality and literal isomorphism hom
are retained. It is invertible for qcqs `f`, flat `j` and arbitrary QC
coefficients, over arbitrary bases and in every natural degree. The
[derived guide](Derived/README.md) records the complete D+ QC-homology
endpoint and its affine-open descent.

[HigherDirectImage/Nonflat](HigherDirectImage/Nonflat.lean) constructs
`higherDirectImageBaseChangeMap` for qcqs `f`, quasicoherent `M`, and arbitrary
Cartesian base change. The actual affine cohomology mates agree on common
refinements; the ordinary module-Hom sheaf glues them. Compatibility is proved
internally. The original chart formula uniquely determines the map, and
coefficient naturality is retained.

[FlatComparison](HigherDirectImage/FlatComparison.lean) proves equality with the
original `higherDirectImageFlatBaseChangeMap` component for flat base change,
under the same qcqs and quasicoherence hypotheses.
[OpenRestriction](HigherDirectImage/Nonflat/OpenRestriction.lean) proves the
composition identity for an arbitrary base map followed by an open immersion,
through the original higher-image open and pullback-composition isomorphisms.

[AffineNormalization](HigherDirectImage/Nonflat/AffineNormalization.lean)
identifies its original affine map and unit pure-tensor formula through native
source and target chart isomorphisms.
[Isomorphism](HigherDirectImage/Nonflat/Isomorphism.lean) transfers the original
scalar isomorphism and residue-section epimorphism criteria. None of these
construction and normalization statements requires flatness or Noetherianity.
The resulting [proper base-change theorems](../DirectImage/Proper/README.md)
retain coherent, relatively flat coefficients over a locally Noetherian base
and allow arbitrary new base schemes.

[NoetherianPushforward](NoetherianPushforward.lean) uses geometric-fibre
concentration to produce finite local rank and invertibility of the original
ordinary `moduleBaseChangeMap`. The original base is locally Noetherian and
may be nonreduced; changes to a new base are arbitrary.
[LineBundleEvaluation](LineBundleEvaluation.lean) constructs the actual
adjunction-counit/dual-evaluation contraction. Its curve application retains
the general Riemann–Roch, high-degree vanishing and cohomological-dimension
inputs, together with the stated fibre genus and degree conditions.

[DegreeZero](HigherDirectImage/DegreeZero.lean) proves
`higherDirectImageFlatBaseChangeMap_zero_unit`: on an actual Cartesian square
with flat base arrow `j`, the installed degree-zero higher-image map commutes
with the original ordinary Cartesian base-change map and the maps to zeroth
right-derived functors. The coefficient `M` is arbitrary; this unit square
needs no quasicoherence, properness or finiteness hypothesis. It does not by
itself assert invertibility of either base-change map.

[ResidueFieldConcentration](ResidueFieldConcentration.lean) turns point-fibre
conditions into `FibreCohomologyConcentrated`, for quasi-compact quasi-separated
`f` and quasicoherent `M`, by field base change (Stacks 02KH). For proper `f`
over a locally Noetherian base, `h^0` is locally constant when the higher fibre
cohomology vanishes. [ResidueFieldPushforward](ResidueFieldPushforward.lean)
gives statement 15a of the Picard plan: on the locus where `h^0 = r` and all
higher fibre cohomology vanishes (Kleiman's (4.8.3), p. 29, with `m = 0`, which
is stronger than 3.10 (v)), the direct image `E = f_*M` is locally free of rank
`r` and commutes with every base change, so `Q = E^∨` is locally free
(3.10 (i)).
