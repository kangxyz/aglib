# The identity component of a group scheme over a field

Let `k` be a field and `G : Over (Spec k)` with `LocallyOfFiniteType G.hom`, and a monoid (`MonObj`)
or group (`GrpObj`) object structure for the cartesian monoidal structure of `Over (Spec k)`.
Declarations are in `AlgebraicGeometry.Scheme.Group`.

[Basic](Basic.lean) defines the unit point `unitPoint G`, the image of the unit section, and the
identity component `identityComponent G : G.left.Opens`, the connected component of the unit point.
It is open by Stacks 04MF (local Noetherianity) and closed (`isClosed_identityComponent`,
`isClopen_identityComponent`). `identityComponentOver G` is `G⁰` over `k`, with inclusion
`identityComponentι G`. It is geometrically connected
(`geometricallyConnected_identityComponentOver`, Stacks 04KV through the unit section). For a group
object, `G⁰` is a group scheme (`grpObjIdentityComponentOver`, through
`CategoryTheory.GrpObj.ofMono`) and the inclusion is a monoid morphism
(`isMonHom_identityComponentι`): `G⁰ ×_k G⁰` is connected (Stacks 0385), so the multiplication maps
it into `G⁰`; the inverse maps the connected `G⁰` into itself because it fixes the unit, and they
factor through the open immersion (`liftIdentityComponent`). The connectedness criteria
`range_subset_identityComponent` and `range_subset_identityComponent_of_section` are public. The
unit point, `G⁰` and its geometric connectedness need only `MonObj`. Of Kleiman, *The Picard
scheme*, Lemma 5.1(3) (pp. 36–37), this gives openness, closedness, the subgroup property and
geometric connectedness; compatibility with field extension is in [BaseChange](BaseChange.lean). Of
Stacks 0B7R it gives (2) and the subgroup property, with `G⁰ ⟶ G` an open immersion onto a closed
set; (3) and (4) are in [FiniteType](FiniteType.lean); the closed-immersion form of (1) is not
stated.

[BaseChange](BaseChange.lean): for a field extension `K/k` and `b : Spec K ⟶ Spec k`, the base
change `(Over.pullback b).obj G` carries the monoid or group structure of the monoidal functor
`Over.pullback b` (Mathlib's `Functor.monObjObj`/`Functor.grpObjObj` under `open scoped
CategoryTheory.Obj`; definitionally the structure of
`Scheme.Group.BaseChange.groupSchemeBaseChange`). `identityComponent_pullback` proves that `(G_K)⁰`
is the preimage of `G⁰` (Kleiman Lemma 5.1(3), p. 37), `isPullback_preimage_identityComponent`
identifies that preimage with `(G⁰)_K`, and `pullback_fst_unitPoint` says that the unit point lies
over the unit point. `pullbackIdentityComponentIso` is the resulting isomorphism of schemes `(G⁰)_K
≅ (G_K)⁰`. The general instance `Scheme.locallyOfFiniteType_over_pullback_obj_hom` is in
[Properties/Noetherian/LocallyNoetherianOverBaseChange](../../Properties/Noetherian/LocallyNoetherianOverBaseChange.lean).

[Irreducible](Irreducible.lean): over an algebraically closed field `k`, every closed point of a
scheme locally of finite type over `k` is the value of a `k`-point
(`exists_point_left_apply_eq_of_isClosed_of_isAlgClosed`, Mathlib's `pointOfClosedPoint`), so
automorphisms of `G` over `k` (right translations, Mathlib's `GrpObj.mulRight`) act transitively on
closed points (`exists_iso_hom_left_apply_eq_of_isClosed_of_isAlgClosed`). A connected group scheme
locally of finite type over an algebraically closed field is irreducible
(`irreducibleSpace_of_connectedSpace_of_isAlgClosed`, Stacks 0B7Q for algebraically closed `k`), by
the homogeneity criterion of
[Topology/Irreducible/LocallyFinite](../../../Topology/Irreducible/LocallyFinite.lean) (Jacobson
from Mathlib's `LocallyOfFiniteType.jacobsonSpace`). Hence `G⁰` is irreducible
(`irreducibleSpace_identityComponent_of_isAlgClosed`). No reduced subgroup scheme and no generic
smoothness are used.

[QuasiCompact](QuasiCompact.lean): the division map `(fst G G / snd G G).left` of a group scheme
over any field is open (`isOpenMap_fst_div_snd_left`: the shear `GrpObj.shearIso` followed by a
universally open projection; Stacks 047K). An irreducible group scheme locally of finite type over
an algebraically closed field is quasi-compact (`compactSpace_of_irreducibleSpace_of_isAlgClosed`,
Stacks 0B7P: the image of `U ×_k U` under `(u₁, u₂) ↦ u₁u₂⁻¹` for a nonempty affine open `U` is open
and contains every closed point, hence is everything by the Jacobson property). Hence `G⁰` is
quasi-compact over an algebraically closed field (`compactSpace_identityComponent_of_isAlgClosed`).

[FiniteType](FiniteType.lean), over an arbitrary field: `(G⁰)_K` is irreducible for every
algebraically closed extension `K`
(`irreducibleSpace_pullback_identityComponentOver_of_isAlgClosed`, via
`pullbackIdentityComponentIso`), so `G⁰` is geometrically irreducible (instance
`geometricallyIrreducible_identityComponentOver`), irreducible (instances
`irreducibleSpace_identityComponentOver_left`, `irreducibleSpace_identityComponent`;
`isIrreducible_identityComponent`), quasi-compact (instances `compactSpace_identityComponent`,
`compactSpace_identityComponentOver_left`, `quasiCompact_identityComponentOver_hom`;
`isCompact_identityComponent`), of finite type
(`quasiCompact_and_locallyOfFiniteType_identityComponentOver`) and a Noetherian scheme (instance
`isNoetherian_identityComponent`). With [Basic](Basic.lean) and [BaseChange](BaseChange.lean) this
gives Kleiman, Lemma 5.1(3), pp. 36–37, and, for `G` locally of finite type, Stacks 0B7R(2)–(4); the
closed-immersion form of 0B7R(1) is not stated.

Not covered: the closed-immersion form of Stacks 0B7R(1) and the group compatibility of
`(G⁰)_K ≅ (G_K)⁰`. Consumers: the Picard identity component
([Picard/IdentityComponent](../../Picard/IdentityComponent.lean); Kleiman Prop. 5.3).
