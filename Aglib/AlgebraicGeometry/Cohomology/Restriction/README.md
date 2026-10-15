# Actual cohomology under open restriction

[Open](Open.lean) gives `sheafHPrimeOpenRestrictionAddEquiv` from native
ambient open cohomology to the unchanged `Sheaf.H` of the actual additive
restriction. It composes the
[exact extension-by-zero Ext comparison](../../../Topology/Sheaves/Cohomology/Restriction.lean)
with the original whole-space comparison, retaining the original coefficient
maps.

`openRestrictionModuleAddSheafIso` is the literal identity identification
with the additive sheaf of `M.restrict U.ι`. The general
`appIso_globalRestriction` formula and `openRestrictionModule_scalar` retain
the original structural scalar action. `moduleHPrimeOpenLinearEquiv X α M U n`
therefore has the actual `moduleHPrimeModuleOfHom X α M n U` action on its
source and `moduleCohomologyModuleOfHom` for `U.ι.appTop.hom.comp α` on its
target. These comparisons require no quasicoherence, compactness,
separatedness or flatness.

[Geometric](Geometric.lean) proves
`moduleCoefficientPullback_restrictUnit` and
`moduleHPrimeOpenLinearEquiv_geometric`. The same comparison is the original
geometric open-cohomology map for `U.ι`, with the actual
`Scheme.Modules.restrictAdjunction` unit, the native preimage-self equality,
and the original whole-space comparison. Its generic additive version has
the same normalization. No compatibility theorem family is assumed.

[Coefficients](Coefficients.lean) gives the raw additive version of the
module restriction-unit formula. For an arbitrary actual local coefficient
arrow `ε : M.restrict U.ι ⟶ N`,
`moduleHPrimeOpenRestrictionAddEquiv_postcomp` identifies its original
`Sheaf.H.map` with the native geometric open map of the restriction unit
postcomposed through `ε`, using the original preimage-self transport and
whole-space comparison. No cartesian, quasicoherence or flatness premise
is needed for this coefficient identity.

[Cartesian](Cartesian.lean) proves the raw native open-cohomology square
for the actual cartesian restriction of a scheme morphism. The two paths
use the original module units and the inverse of the actual native
pullback/restriction mate. Composition, equality of composite morphisms
and open naturality retain the original maps and actual preimage transports.

[Cartesian/Geometric](Cartesian/Geometric.lean) proves
`moduleHPrimeOpenRestrictionAddEquiv_pullback`. The original open equivalences
intertwine the geometric unit map with the actual cohomology pullback on
the restricted source, after the original coefficient map of the inverse
cartesian mate. The identity holds for arbitrary modules, morphisms and
degrees, without flatness or quasicoherence. This is the unit square used
by the finite-union Mayer–Vietoris proof of qcqs flat base change.

[Top](Top.lean) proves
`moduleHPrimeOpenLinearEquiv_restriction_top_geometric`. Restricting the
original whole-space `Sheaf.H'` class to `V` and applying the existing open
linear comparison equals the original `moduleCohomologyMapAlong` for
`V.ι` and its actual `restrictAdjunction` unit, after the existing whole-space
linear comparison. The proof retains the original structural scalar actions,
native preimage-self transport and original open-cohomology geometric map.
It holds in every degree for arbitrary coefficients, without quasicoherence,
flatness or geometric finiteness. The leaf passed alone under the default
budget with receipt `1792104446255330000-64515`.
The external `OpenRestrictionTopGeometricConsumer.lean` passed with receipt
`1792104521632656000-65865`, retaining arbitrary universe `u`, all degrees
and the original actions. The normalization uses only `propext`,
`Classical.choice` and `Quot.sound`.
