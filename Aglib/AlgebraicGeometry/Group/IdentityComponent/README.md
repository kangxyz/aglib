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
set; the closed-immersion form of (1), geometric irreducibility (3) and quasi-compactness (4) are
not stated.

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

Not covered: irreducibility over `k̄` (Stacks 0B7Q), quasi-compactness (Stacks 0B7P), finite type,
geometric irreducibility, the group compatibility of `(G⁰)_K ≅ (G_K)⁰`, and the Picard
specialization. Consumers: the planned Picard identity component (Kleiman Prop. 5.3).
