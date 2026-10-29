/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # A fixed sheaf pulled back to an inverse scheme diagram

A cone in the opposite category specifies the structural morphisms to a fixed
base scheme. Its fixed coefficient sheaf gives an actual compatible system,
with transitions obtained from the original inverse-image triangle isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u uI vI
attribute [local instance] hasSheafifyLarge

open Continuity

private theorem triangle_id_transport {X Y : Scheme.{u}} (f : Y ⟶ X)
    (e : Y ⟶ Y) (he : e = 𝟙 Y) (h : e ≫ f = f)
    (F : AbelianSheaf.{u, u + 1} X) :
    (pullbackTriangleIso f f e h).inv.app F =
      (eqToIso (congrArg inverseImage he) ≪≫ inverseImageId Y).hom.app
        ((inverseImage f).obj F) := by
  subst e
  apply (cancel_epi ((pullbackTriangleIso f f (𝟙 Y) h).hom.app F)).1
  rw [Iso.hom_inv_id_app, pullbackTriangleIso_id]
  simp only [eqToIso_refl, Iso.refl_trans, Iso.inv_hom_id_app]
  rfl

private theorem triangle_comp_transport {X Y Z W : Scheme.{u}}
    (f : W ⟶ X) (g : Z ⟶ X) (h : Y ⟶ X) (a : Y ⟶ Z) (b : Z ⟶ W)
    (d : Y ⟶ W) (hd : d = a ≫ b) (hb : b ≫ f = g) (ha : a ≫ g = h)
    (hda : d ≫ f = h) (F : AbelianSheaf.{u, u + 1} X) :
    (pullbackTriangleIso h f d hda).inv.app F =
      (eqToIso (congrArg inverseImage hd) ≪≫ inverseImageComp b a).hom.app
          ((inverseImage f).obj F) ≫
        (inverseImage a).map ((pullbackTriangleIso g f b hb).inv.app F) ≫
          (pullbackTriangleIso h g a ha).inv.app F := by
  subst d
  simpa only [eqToIso_refl, Iso.refl_trans] using
    (pullbackTriangleIso_comp_inv f g h a b hb ha F).symm

private theorem triangle_comp_transport_nat {X Y Z W : Scheme.{u}}
    (f : W ⟶ X) (g : Z ⟶ X) (h : Y ⟶ X) (a : Y ⟶ Z) (b : Z ⟶ W)
    (d : Y ⟶ W) (hd : d = a ≫ b) (hb : b ≫ f = g) (ha : a ≫ g = h)
    (hda : d ≫ f = h) :
    (pullbackTriangleIso h f d hda).inv =
      Functor.whiskerLeft (inverseImage f)
          (eqToIso (congrArg inverseImage hd) ≪≫ inverseImageComp b a).hom ≫
        (Functor.associator (inverseImage f) (inverseImage b) (inverseImage a)).inv ≫
        Functor.whiskerRight (pullbackTriangleIso g f b hb).inv (inverseImage a) ≫
          (pullbackTriangleIso h g a ha).inv := by
  apply NatTrans.ext
  funext F
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] using
      triangle_comp_transport f g h a b d hd hb ha hda F

variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
    (b : Cone Y) (F : AbelianSheaf.{u, u + 1} b.pt.unop)

/-- The original inverse-image transition for the fixed coefficient sheaf. -/
def pullbackCoefficientTransition {i j : I} (a : i ⟶ j) :
    (inverseImage (Y.map a).unop).obj ((inverseImage (b.π.app i).unop).obj F) ⟶
      (inverseImage (b.π.app j).unop).obj F :=
  (pullbackTriangleIso (b.π.app j).unop (b.π.app i).unop (Y.map a).unop
    (congrArg Quiver.Hom.unop (b.w a))).inv.app F

/-- Original triangle transitions obey the actual diagram identity comparison. -/
theorem pullbackCoefficientTransition_id (i : I) :
    pullbackCoefficientTransition Y b F (𝟙 i) =
      (diagramInverseImageId Y i).hom.app ((inverseImage (b.π.app i).unop).obj F) :=
  triangle_id_transport (b.π.app i).unop (Y.map (𝟙 i)).unop
    (congrArg Quiver.Hom.unop (Y.map_id i))
    (congrArg Quiver.Hom.unop (b.w (𝟙 i))) F

private theorem pullbackCoefficientTransition_comp_nat {i j k : I}
    (a : i ⟶ j) (d : j ⟶ k) :
    (pullbackTriangleIso (b.π.app k).unop (b.π.app i).unop (Y.map (a ≫ d)).unop
      (congrArg Quiver.Hom.unop (b.w (a ≫ d)))).inv =
      Functor.whiskerLeft (inverseImage (b.π.app i).unop)
          (diagramInverseImageComp Y a d).hom ≫
        (Functor.associator (inverseImage (b.π.app i).unop)
          (inverseImage (Y.map a).unop) (inverseImage (Y.map d).unop)).inv ≫
        Functor.whiskerRight
          (pullbackTriangleIso (b.π.app j).unop (b.π.app i).unop (Y.map a).unop
            (congrArg Quiver.Hom.unop (b.w a))).inv (inverseImage (Y.map d).unop) ≫
        (pullbackTriangleIso (b.π.app k).unop (b.π.app j).unop (Y.map d).unop
          (congrArg Quiver.Hom.unop (b.w d))).inv :=
  triangle_comp_transport_nat (b.π.app i).unop (b.π.app j).unop (b.π.app k).unop
    (Y.map d).unop (Y.map a).unop (Y.map (a ≫ d)).unop
    (congrArg Quiver.Hom.unop (Y.map_comp a d))
    (congrArg Quiver.Hom.unop (b.w a))
    (congrArg Quiver.Hom.unop (b.w d))
    (congrArg Quiver.Hom.unop (b.w (a ≫ d)))

/-- Original triangle transitions obey the actual diagram composition comparison. -/
theorem pullbackCoefficientTransition_comp {i j k : I} (a : i ⟶ j) (d : j ⟶ k) :
    pullbackCoefficientTransition Y b F (a ≫ d) =
      (diagramInverseImageComp Y a d).hom.app ((inverseImage (b.π.app i).unop).obj F) ≫
        (inverseImage (Y.map d).unop).map (pullbackCoefficientTransition Y b F a) ≫
          pullbackCoefficientTransition Y b F d := by
  have h := congrArg (fun t => t.app F) (pullbackCoefficientTransition_comp_nat Y b a d)
  simpa only [pullbackCoefficientTransition, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] using h

/-- Pulling back one fixed sheaf gives a genuine compatible coefficient system. -/
def pullbackCoefficientSystem : DiagramCoefficientSystem Y :=
  InjectiveSystem.System.ofLeft (diagramAdjunctionData Y)
    (fun i => (inverseImage (b.π.app i).unop).obj F)
    (pullbackCoefficientTransition Y b F)
    (fun i => by
      rw [leftIdIso_eq_diagramInverseImageId Y i]
      exact pullbackCoefficientTransition_id Y b F i)
    (fun a d => by
      rw [leftCompIso_eq_diagramInverseImageComp Y a d]
      exact pullbackCoefficientTransition_comp Y b F a d)

/-- The inverse transition is literally the original triangle identification. -/
@[simp]
theorem diagramInverseTransition_pullbackCoefficientSystem {i j : I} (a : i ⟶ j) :
    diagramInverseTransition Y (pullbackCoefficientSystem Y b F) a =
      pullbackCoefficientTransition Y b F a := by
  change (pullbackCoefficientSystem Y b F).leftMap (diagramAdjunctionData Y) a = _
  exact InjectiveSystem.System.ofLeft_leftMap (diagramAdjunctionData Y)
    (fun i => (inverseImage (b.π.app i).unop).obj F)
    (fun {i j} (a : i ⟶ j) => pullbackCoefficientTransition Y b F a)
    (fun i => by
      rw [leftIdIso_eq_diagramInverseImageId Y i]
      exact pullbackCoefficientTransition_id Y b F i)
    (fun a d => by
      rw [leftCompIso_eq_diagramInverseImageComp Y a d]
      exact pullbackCoefficientTransition_comp Y b F a d) a

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
