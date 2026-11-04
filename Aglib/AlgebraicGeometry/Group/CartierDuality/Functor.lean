/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Coordinate

/-!
# Contravariance of the native finite Cartier dual

Coordinate pullback uses the existing fully faithful Hopf-Spec correspondence
and the original coordinate isomorphisms. Its ring map is proved to be the
original global-sections pullback. Dual morphisms then use the original linear
transpose and native Spec, on the same finite group objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped Module.Dual.FiniteDual

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The existing fully faithful Hopf-Spec preimage, before choosing coordinates. -/
def specGroupPullback {A B : CommHopfAlgCat.{u} k} (f : specGroup A ⟶ specGroup B) :
    B ⟶ A :=
  ((AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (X := op A) (Y := op B) f).unop

/-- The original native Spec map of its fully faithful preimage. -/
theorem hopfSpec_specGroupPullback {A B : CommHopfAlgCat.{u} k}
    (f : specGroup A ⟶ specGroup B) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map (specGroupPullback f).op = f := by
  exact (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f

variable {G H K : Grp (FScheme k)} [IsFinite G.X.hom] [IsFinite H.X.hom]
  [IsFinite K.X.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback on the selected original coordinate Hopf algebras. -/
def coordinateMap (f : G ⟶ H) : coordinateHopf H ⟶ coordinateHopf G :=
  specGroupPullback (A := coordinateHopf G) (B := coordinateHopf H)
    ((coordinateSpecIso G).hom ≫ f ≫ (coordinateSpecIso H).inv)

/-- The whole native Spec comparison for the actual coordinate pullback. -/
theorem hopfSpec_coordinateMap (f : G ⟶ H) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map (coordinateMap f).op =
      (coordinateSpecIso G).hom ≫ f ≫ (coordinateSpecIso H).inv := by
  exact hopfSpec_specGroupPullback (A := coordinateHopf G) (B := coordinateHopf H) _

@[simp]
theorem coordinateMap_id : coordinateMap (𝟙 G) = 𝟙 (coordinateHopf G) := by
  apply Quiver.Hom.op_inj
  apply (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [hopfSpec_coordinateMap, op_id]
  have h := (coordinateSpecIso G).hom_inv_id.trans
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map_id (op (coordinateHopf G))).symm
  simpa only [specGroup, Category.id_comp] using h

/-- Coordinate pullback reverses composition on the original group morphisms. -/
theorem coordinateMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    coordinateMap (f ≫ g) = coordinateMap g ≫ coordinateMap f := by
  have h : ((coordinateSpecIso G).hom ≫ f ≫ (coordinateSpecIso H).inv) ≫
      ((coordinateSpecIso H).hom ≫ g ≫ (coordinateSpecIso K).inv) =
      (coordinateSpecIso G).hom ≫ (f ≫ g) ≫ (coordinateSpecIso K).inv := by
    simp [Category.assoc]
  apply Quiver.Hom.op_inj
  apply (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [hopfSpec_coordinateMap, op_comp, CategoryTheory.Functor.map_comp,
    hopfSpec_coordinateMap, hopfSpec_coordinateMap]
  exact h.symm

/-- The actual coordinate pullback detects equality of original finite group morphisms. -/
theorem coordinateMap_injective :
    Function.Injective (coordinateMap (G := G) (H := H)) := by
  intro f g hfg
  apply (cancel_epi (coordinateSpecIso G).hom).mp
  apply (cancel_mono (coordinateSpecIso H).inv).mp
  have h := congrArg
    (fun q : coordinateHopf H ⟶ coordinateHopf G =>
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map q.op) hfg
  rw [hopfSpec_coordinateMap, hopfSpec_coordinateMap] at h
  simpa only [Category.assoc, specGroup] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying coordinate ring map is exactly the original global-sections pullback. -/
theorem coordinateMap_appTop (f : G ⟶ H) :
    CommRingCat.ofHom (coordinateMap f).hom.toAlgHom.toRingHom = f.hom.hom.left.appTop := by
  have hn : (coordinateSpecIso G).inv ≫
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map (coordinateMap f).op =
      f ≫ (coordinateSpecIso H).inv := by
    rw [hopfSpec_coordinateMap]
    simp
  have hs := congrArg
    (fun q : G ⟶ specGroup (coordinateHopf H) => q.hom.hom.left) hn
  change (coordinateSpecIso G).inv.hom.hom.left ≫
      Spec.map (CommRingCat.ofHom (coordinateMap f).hom.toAlgHom.toRingHom) =
      f.hom.hom.left ≫ (coordinateSpecIso H).inv.hom.hom.left at hs
  rw [coordinateSpecIso_inv_left, coordinateSpecIso_inv_left] at hs
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply Spec.map_injective
  apply (cancel_epi G.X.left.toSpecΓ).mp
  exact hs.trans (Scheme.toSpecΓ_naturality f.hom.hom.left)

variable [IsCommMonObj G.X] [IsCommMonObj H.X] [IsCommMonObj K.X]

/-- The actual contravariant dual morphism: native Spec of the original transpose. -/
def dualMap (f : G ⟶ H) : dualGroup H ⟶ dualGroup G :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map
    (CommHopfAlgCat.ofHom (coordinateMap f).hom.dual).op

@[simp]
theorem dualMap_id : dualMap (𝟙 G) = 𝟙 (dualGroup G) := by
  unfold dualMap
  rw [coordinateMap_id]
  change (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map
    (CommHopfAlgCat.ofHom (BialgHom.id k (coordinateHopf G)).dual).op = _
  rw [BialgHom.dual_id, CommHopfAlgCat.ofHom_id, op_id]
  exact (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map_id _

/-- The same actual dual maps reverse composition. -/
theorem dualMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  unfold dualMap
  rw [coordinateMap_comp, CommHopfAlgCat.hom_comp, BialgHom.dual_comp,
    CommHopfAlgCat.ofHom_comp, op_comp, CategoryTheory.Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Group.CartierDuality
