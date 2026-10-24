/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Connected.RationalPoint
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyConnected
public import Aglib.CategoryTheory.Monoidal.GrpObjOfMono
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The identity component of a group scheme over a field

Let `k` be a field and `G` a group scheme over `k`, that is `G : Over (Spec k)` with a group
object structure for the cartesian monoidal structure of `Over (Spec k)`, and assume that `G` is
locally of finite type over `k`. Its identity component
`AlgebraicGeometry.Scheme.Group.identityComponent G` is the connected component of the unit point
`unitPoint G`, the image of the unit section. This module proves the following parts of Stacks
Project, Tag 0B7R, and of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Lemma 5.1(3),
pp. 36–37:

* `G⁰` is open, because `G` is locally Noetherian and hence locally connected (Stacks 04MF), and
  closed (`isClosed_identityComponent`);
* `G⁰`, as a scheme over `k` (`identityComponentOver G`), is geometrically connected
  (`geometricallyConnected_identityComponentOver`), because it is connected and the unit is a
  rational point of it (Stacks 04KV);
* `G⁰` is a subgroup: `identityComponentOver G` is a group object
  (`grpObjIdentityComponentOver`) and the inclusion `identityComponentι G` is a monoid morphism
  (`isMonHom_identityComponentι`).

For the subgroup step, `G⁰ ×_k G⁰` is connected (Mathlib: a geometrically connected scheme over a
field times a connected one is connected, Stacks 0385), so its image under the multiplication is
a connected set containing the unit point, hence lies in `G⁰`; the inverse is handled in the same
way. The multiplication, inverse and unit then factor through the open immersion `G⁰ ⟶ G`
(`liftIdentityComponent`, from Mathlib's `IsOpenImmersion.lift`), and
`CategoryTheory.GrpObj.ofMono` transfers the group axioms. Stacks 0B7R argues with flat closed
immersions instead (Stacks 04PW); the open immersion is simpler here because `G⁰` is open.

The unit point, the identity component and its geometric connectedness need only a monoid object
structure; the subgroup statements use the group structure.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group

universe u

variable {k : Type u} [Field k] (G : Over (Spec (.of k)))

section MonObj

variable [MonObj G]

/-- **The unit point** of a monoid scheme over a field: the image of the unit section. -/
def unitPoint : G.left := η[G].left (IsLocalRing.closedPoint k)

/-- Every point of `Spec k` maps to the unit point under the unit section. -/
theorem one_left_apply (x : Spec (.of k)) : η[G].left x = unitPoint G := by
  rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]
  rfl

variable [LocallyOfFiniteType G.hom]

/-- **The identity component** `G⁰`: the connected component of the unit point. It is open
because `G` is locally Noetherian, hence locally connected (Stacks 04MF). -/
def identityComponent : G.left.Opens where
  carrier := connectedComponent (unitPoint G)
  is_open' := by
    have := LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) G.hom
    exact isOpen_connectedComponent

@[simp]
theorem coe_identityComponent :
    (identityComponent G : Set G.left) = connectedComponent (unitPoint G) :=
  rfl

/-- The unit point lies in the identity component. -/
theorem unitPoint_mem_identityComponent : unitPoint G ∈ identityComponent G :=
  mem_connectedComponent

/-- **The identity component is closed.** -/
theorem isClosed_identityComponent : IsClosed (identityComponent G : Set G.left) :=
  isClosed_connectedComponent

/-- The identity component is open and closed. -/
theorem isClopen_identityComponent : IsClopen (identityComponent G : Set G.left) :=
  ⟨isClosed_identityComponent G, (identityComponent G).isOpen⟩

/-- The identity component is connected. -/
theorem isConnected_identityComponent :
    _root_.IsConnected (identityComponent G : Set G.left) :=
  isConnected_connectedComponent

/-- The identity component is connected, as an open subscheme. -/
instance connectedSpace_identityComponent : ConnectedSpace (identityComponent G).toScheme :=
  isConnected_iff_connectedSpace.mp (isConnected_identityComponent G)

/-- **The identity component as a scheme over `k`.** -/
def identityComponentOver : Over (Spec (.of k)) :=
  Over.mk ((identityComponent G).ι ≫ G.hom)

@[simp]
theorem identityComponentOver_left :
    (identityComponentOver G).left = (identityComponent G).toScheme :=
  rfl

@[simp]
theorem identityComponentOver_hom :
    (identityComponentOver G).hom = (identityComponent G).ι ≫ G.hom :=
  rfl

/-- The identity component is connected, as a scheme over `k`. -/
instance connectedSpace_identityComponentOver_left :
    ConnectedSpace (identityComponentOver G).left :=
  connectedSpace_identityComponent G

/-- `G⁰` is locally of finite type over `k`. -/
instance locallyOfFiniteType_identityComponentOver_hom :
    LocallyOfFiniteType (identityComponentOver G).hom :=
  inferInstanceAs (LocallyOfFiniteType ((identityComponent G).ι ≫ G.hom))

/-- The structure morphism of `G⁰` is universally open, as is every morphism to the spectrum
of a field. -/
instance universallyOpen_identityComponentOver_hom :
    UniversallyOpen (identityComponentOver G).hom :=
  inferInstanceAs (UniversallyOpen (Y := Spec (.of k)) (identityComponentOver G).hom)

/-- **The inclusion** `G⁰ ⟶ G` over `k`. -/
def identityComponentι : identityComponentOver G ⟶ G :=
  Over.homMk (identityComponent G).ι rfl

@[simp]
theorem identityComponentι_left : (identityComponentι G).left = (identityComponent G).ι :=
  rfl

/-- The inclusion of the identity component is an open immersion. -/
instance isOpenImmersion_identityComponentι_left : IsOpenImmersion (identityComponentι G).left :=
  inferInstanceAs (IsOpenImmersion (identityComponent G).ι)

/-- The inclusion of the identity component is a monomorphism. -/
instance mono_identityComponentι : Mono (identityComponentι G) :=
  have : Mono (identityComponentι G).left := inferInstanceAs (Mono (identityComponent G).ι)
  Over.mono_of_mono_left _

/-- **Factorization through the identity component**: a morphism into `G` whose image lies in
`G⁰` factors through the inclusion. -/
def liftIdentityComponent {T : Over (Spec (.of k))} (f : T ⟶ G)
    (hf : Set.range f.left ⊆ identityComponent G) : T ⟶ identityComponentOver G :=
  Over.homMk
    (IsOpenImmersion.lift (identityComponent G).ι f.left (by rwa [Scheme.Opens.range_ι]) :
      T.left ⟶ (identityComponent G).toScheme)
    ((IsOpenImmersion.lift_fac_assoc (identityComponent G).ι f.left _ G.hom).trans (Over.w f))

@[reassoc (attr := simp)]
theorem liftIdentityComponent_ι {T : Over (Spec (.of k))} (f : T ⟶ G)
    (hf : Set.range f.left ⊆ identityComponent G) :
    liftIdentityComponent G f hf ≫ identityComponentι G = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac (identityComponent G).ι f.left _)

/-- A morphism from a connected scheme to `G` that sends some point to the unit point has image
in `G⁰`. -/
theorem range_subset_identityComponent {T : Scheme.{u}} [ConnectedSpace T] (f : T ⟶ G.left)
    (t : T) (ht : f t = unitPoint G) : Set.range f ⊆ identityComponent G :=
  (isConnected_range f.continuous).isPreconnected.subset_connectedComponent ⟨t, ht⟩

/-- A morphism over `k` from a scheme with connected underlying space to `G`, which maps a
rational point to the unit, has image in `G⁰`. -/
theorem range_subset_identityComponent_of_section {T : Over (Spec (.of k))}
    [ConnectedSpace T.left] (f : T ⟶ G) (t : 𝟙_ (Over (Spec (.of k))) ⟶ T) (ht : t ≫ f = η[G]) :
    Set.range f.left ⊆ identityComponent G :=
  range_subset_identityComponent G f.left (t.left (IsLocalRing.closedPoint k))
    (congrArg (fun φ : 𝟙_ (Over (Spec (.of k))) ⟶ G => φ.left (IsLocalRing.closedPoint k)) ht)

/-- The unit section has image in `G⁰`. -/
theorem range_one_subset_identityComponent : Set.range η[G].left ⊆ identityComponent G :=
  range_subset_identityComponent G (T := Spec (.of k)) η[G].left (IsLocalRing.closedPoint k) rfl

/-- The unit section of `G⁰`. -/
def identityComponentOne : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver G :=
  liftIdentityComponent G η[G] (range_one_subset_identityComponent G)

@[reassoc (attr := simp)]
theorem identityComponentOne_ι : identityComponentOne G ≫ identityComponentι G = η[G] :=
  liftIdentityComponent_ι ..

/-- The unit is a rational point of `G⁰`. -/
theorem identityComponentOne_left_comp_hom :
    (identityComponentOne G).left ≫ (identityComponentOver G).hom = 𝟙 (Spec (.of k)) :=
  Over.w (identityComponentOne G)

/-- **The identity component is geometrically connected** (Stacks 0B7R, proof; Kleiman,
Lemma 5.1(3), proof, p. 37): it is connected and the
unit is a rational point of it (Stacks 04KV). -/
instance geometricallyConnected_identityComponentOver :
    GeometricallyConnected (identityComponentOver G).hom :=
  Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section
    (identityComponentOver G).hom (identityComponentOne G).left
    (identityComponentOne_left_comp_hom G)

/-- `G⁰ ×_k G⁰` is connected (Stacks 0385). -/
instance connectedSpace_identityComponentOver_tensorObj_left :
    ConnectedSpace (identityComponentOver G ⊗ identityComponentOver G).left :=
  inferInstanceAs (ConnectedSpace
    (pullback (identityComponentOver G).hom (identityComponentOver G).hom : Scheme.{u}))

/-- **`G⁰` is closed under the multiplication.** -/
theorem range_mul_subset_identityComponent :
    Set.range ((identityComponentι G ⊗ₘ identityComponentι G) ≫ μ[G]).left ⊆
      identityComponent G := by
  have hη : lift (identityComponentOne G) (identityComponentOne G) ≫
      (identityComponentι G ⊗ₘ identityComponentι G) ≫ μ[G] = η[G] := by
    rw [lift_map_assoc, identityComponentOne_ι]
    have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Spec (.of k))))) η[G]
    rwa [Category.id_comp] at this
  exact range_subset_identityComponent_of_section G _
    (lift (identityComponentOne G) (identityComponentOne G)) hη

/-- The multiplication of `G⁰`. -/
def identityComponentMul :
    identityComponentOver G ⊗ identityComponentOver G ⟶ identityComponentOver G :=
  liftIdentityComponent G _ (range_mul_subset_identityComponent G)

@[reassoc (attr := simp)]
theorem identityComponentMul_ι :
    identityComponentMul G ≫ identityComponentι G =
      (identityComponentι G ⊗ₘ identityComponentι G) ≫ μ[G] :=
  liftIdentityComponent_ι ..

end MonObj

section GrpObj

variable [GrpObj G] [LocallyOfFiniteType G.hom]

/-- **`G⁰` is closed under the inverse.** -/
theorem range_inv_subset_identityComponent :
    Set.range (identityComponentι G ≫ ι[G]).left ⊆ identityComponent G :=
  range_subset_identityComponent_of_section G _ (identityComponentOne G)
    (by rw [identityComponentOne_ι_assoc, GrpObj.one_inv])

/-- The inverse of `G⁰`. -/
def identityComponentInv : identityComponentOver G ⟶ identityComponentOver G :=
  liftIdentityComponent G _ (range_inv_subset_identityComponent G)

@[reassoc (attr := simp)]
theorem identityComponentInv_ι :
    identityComponentInv G ≫ identityComponentι G = identityComponentι G ≫ ι[G] :=
  liftIdentityComponent_ι ..

/-- **The identity component is a group scheme over `k`** (Stacks 0B7R). -/
instance grpObjIdentityComponentOver : GrpObj (identityComponentOver G) :=
  GrpObj.ofMono (identityComponentι G) (identityComponentOne G) (identityComponentMul G)
    (identityComponentInv G) (identityComponentOne_ι G) (identityComponentMul_ι G)
    (identityComponentInv_ι G)

/-- **The inclusion of the identity component is a monoid morphism.** -/
instance isMonHom_identityComponentι : IsMonHom (identityComponentι G) :=
  GrpObj.isMonHom_ofMono (identityComponentι G) (identityComponentOne G) (identityComponentMul G)
    (identityComponentInv G) (identityComponentOne_ι G) (identityComponentMul_ι G)
    (identityComponentInv_ι G)

/-- The unit of `G⁰` is `identityComponentOne G`. -/
theorem one_identityComponentOver : η[identityComponentOver G] = identityComponentOne G :=
  rfl

/-- The multiplication of `G⁰` is `identityComponentMul G`. -/
theorem mul_identityComponentOver : μ[identityComponentOver G] = identityComponentMul G :=
  rfl

/-- The inverse of `G⁰` is `identityComponentInv G`. -/
theorem inv_identityComponentOver : ι[identityComponentOver G] = identityComponentInv G :=
  rfl

end GrpObj

end AlgebraicGeometry.Scheme.Group
