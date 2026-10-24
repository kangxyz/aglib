/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic
public import Aglib.Topology.Irreducible.LocallyFinite
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Irreducibility of the identity component over an algebraically closed field

Let `k` be an algebraically closed field and `G` a group scheme locally of finite type over `k`,
that is `G : Over (Spec k)` with a group object structure and `LocallyOfFiniteType G.hom`. This
module proves:

* translations act transitively on the closed points of `G`
  (`exists_iso_hom_left_apply_eq_of_isClosed_of_isAlgClosed`): for closed points `x`, `y` there is
  an automorphism of `G` over `k` sending `x` to `y`, the right translation by `x⁻¹y` (Mathlib's
  `CategoryTheory.GrpObj.mulRight`), because every closed point is the value of a `k`-point
  (Mathlib's `AlgebraicGeometry.pointOfClosedPoint`);
* **if `G` is connected, it is irreducible**
  (`AlgebraicGeometry.Scheme.Group.irreducibleSpace_of_connectedSpace_of_isAlgClosed`; Stacks
  Project, Tag 0B7Q, for algebraically closed `k`);
* hence **the identity component `G⁰` is irreducible**
  (`AlgebraicGeometry.Scheme.Group.irreducibleSpace_identityComponent_of_isAlgClosed`; Stacks
  0B7R(3) and Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Lemma 5.1(3), p. 37, over an
  algebraically closed field).

The proof is the translation argument: `G` is Jacobson (Mathlib's
`LocallyOfFiniteType.jacobsonSpace`), locally Noetherian and connected, and translations are
homeomorphisms acting transitively on closed points, so the homogeneity criterion
`irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints` of
`Aglib.Topology.Irreducible.LocallyFinite` applies. It uses no reduced subgroup scheme: Kleiman
(p. 37) passes to `(G⁰)_red` and uses generic smoothness, and Stacks 0B7Q makes the reduced
irreducible component through the identity a closed subgroup scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group

universe u

variable {k : Type u} [Field k] (G : Over (Spec (.of k)))

/-- **Closed points are rational** over an algebraically closed field: every closed point of a
scheme `G` locally of finite type over `k` is the value of a `k`-point of `G`. -/
theorem exists_point_left_apply_eq_of_isClosed_of_isAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType G.hom] {z : G.left} (hz : IsClosed {z}) :
    ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ G, p.left (IsLocalRing.closedPoint k) = z :=
  ⟨Over.homMk (pointOfClosedPoint G.hom z hz) (pointOfClosedPoint_comp G.hom z hz),
    pointOfClosedPoint_apply G.hom z hz _⟩

/-- **Translations act transitively on closed points.** For closed points `x`, `y` of a group
scheme `G` locally of finite type over an algebraically closed field, there is an automorphism of
`G` over `k` sending `x` to `y` (the right translation by `x⁻¹y`). -/
theorem exists_iso_hom_left_apply_eq_of_isClosed_of_isAlgClosed [IsAlgClosed k] [GrpObj G]
    [LocallyOfFiniteType G.hom] {x y : G.left} (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ α : G ≅ G, α.hom.left x = y := by
  obtain ⟨px, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hx
  obtain ⟨py, rfl⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hy
  refine ⟨(GrpObj.mulRight px).symm ≪≫ GrpObj.mulRight py, ?_⟩
  have hα : px ≫ ((GrpObj.mulRight px).symm ≪≫ GrpObj.mulRight py).hom = py := by
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  exact congrArg (fun φ : 𝟙_ (Over (Spec (.of k))) ⟶ G => φ.left (IsLocalRing.closedPoint k)) hα

/-- **A connected group scheme locally of finite type over an algebraically closed field is
irreducible** (Stacks 0B7Q, for algebraically closed `k`), by the translation argument. -/
theorem irreducibleSpace_of_connectedSpace_of_isAlgClosed [IsAlgClosed k] [GrpObj G]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  refine irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints
    (fun x => ?_) fun x hx y hy => ?_
  · obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) (by simp)
    have : IsNoetherianRing Γ(G.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨U, U.isOpen.mem_nhds hxU, noetherianSpace_of_isAffineOpen U hU⟩
  · obtain ⟨α, hα⟩ := exists_iso_hom_left_apply_eq_of_isClosed_of_isAlgClosed G hx hy
    exact ⟨Scheme.homeoOfIso ((Over.forget _).mapIso α), hα⟩

variable [GrpObj G] [LocallyOfFiniteType G.hom]

/-- **The identity component is irreducible over an algebraically closed field** (Stacks 0B7Q
applied to `G⁰`; Kleiman, Lemma 5.1(3), p. 37). Over an arbitrary field, `G⁰` is geometrically
irreducible (`Aglib.AlgebraicGeometry.Group.IdentityComponent.FiniteType`). -/
theorem irreducibleSpace_identityComponent_of_isAlgClosed [IsAlgClosed k] :
    IrreducibleSpace (identityComponent G).toScheme :=
  irreducibleSpace_of_connectedSpace_of_isAlgClosed (identityComponentOver G)

end AlgebraicGeometry.Scheme.Group
