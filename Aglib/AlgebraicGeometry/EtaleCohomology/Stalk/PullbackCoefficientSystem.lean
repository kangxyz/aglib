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

namespace CategoryTheory.InjectiveSystem

universe uI vI uA vA

/-- Construct the actual right-adjoint system from coherent left-adjoint transitions. -/
def System.ofLeftMaps {I : Type uI} [Category.{vI} I]
    {A : I → Type uA} [∀ i, Category.{vA} (A i)] (D : AdjunctionData A)
    (P : ∀ i, A i) (φ : ∀ {i j}, (a : i ⟶ j) → (D.left a).obj (P i) ⟶ P j)
    (hId : ∀ i, φ (𝟙 i) = (D.leftIdIso i).hom.app (P i))
    (hComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (D.leftCompIso a b).hom.app (P i) ≫
        (D.left b).map (φ a) ≫ φ b) : System D where
  obj := P
  map a := (D.adj a).homEquiv _ _ (φ a)
  map_id i := by
    rw [hId]
    have ht := homEquiv_precomp_conjugate Adjunction.id (D.adj (𝟙 i))
      (D.leftIdIso i).hom (𝟙 (P i))
    have hm : conjugateEquiv Adjunction.id (D.adj (𝟙 i)) (D.leftIdIso i).hom =
        (D.idIso i).inv := Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _
    rw [hm] at ht
    have hid : Adjunction.id.homEquiv (P i) (P i) (𝟙 (P i)) = 𝟙 (P i) :=
      (Adjunction.homEquiv_id Adjunction.id (P i)).trans rfl
    have ht' := ht.trans (congrArg
      (fun k => k ≫ (D.idIso i).inv.app (P i)) hid)
    have hleft := congrArg ((D.adj (𝟙 i)).homEquiv (P i) (P i))
      (Category.comp_id ((D.leftIdIso i).hom.app (P i)))
    have hvalue := hleft.symm.trans (ht'.trans (Category.id_comp _))
    exact (congrArg (fun k => k ≫ (D.idIso i).hom.app (P i)) hvalue).trans
      ((D.idIso i).inv_hom_id_app (P i))
  map_comp a b := by
    rw [hComp, homEquiv_precomp_conjugate ((D.adj a).comp (D.adj b))
      (D.adj (a ≫ b)) (D.leftCompIso a b).hom]
    have hm : conjugateEquiv ((D.adj a).comp (D.adj b)) (D.adj (a ≫ b))
        (D.leftCompIso a b).hom = (D.compIso a b).inv :=
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
    rw [hm, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      Adjunction.comp_homEquiv]
    change (D.adj a).homEquiv _ _ ((D.adj b).homEquiv _ _
      ((D.left b).map (φ a) ≫ φ b)) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

/-- Keep explicit comparison choices at the abstract adjunction boundary. -/
def System.ofLeftMapsWithComparisons {I : Type uI} [Category.{vI} I]
    {A : I → Type uA} [∀ i, Category.{vA} (A i)] (D : AdjunctionData A)
    (eId : ∀ i, D.left (𝟙 i) ≅ 𝟭 (A i))
    (eComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
      D.left (a ≫ b) ≅ D.left a ⋙ D.left b)
    (heId : ∀ i, D.leftIdIso i = eId i)
    (heComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k), D.leftCompIso a b = eComp a b)
    (P : ∀ i, A i) (φ : ∀ {i j}, (a : i ⟶ j) → (D.left a).obj (P i) ⟶ P j)
    (hId : ∀ i, φ (𝟙 i) = (eId i).hom.app (P i))
    (hComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (eComp a b).hom.app (P i) ≫ (D.left b).map (φ a) ≫ φ b) :
    System D :=
  System.ofLeftMaps D P φ
    (fun i => by rw [heId]; exact hId i)
    (fun a b => by rw [heComp]; exact hComp a b)

end CategoryTheory.InjectiveSystem

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
  InjectiveSystem.System.ofLeftMapsWithComparisons (diagramAdjunctionData Y)
    (diagramInverseImageId Y) (diagramInverseImageComp Y)
    (leftIdIso_eq_diagramInverseImageId Y) (leftCompIso_eq_diagramInverseImageComp Y)
    (fun i => (inverseImage (b.π.app i).unop).obj F)
    (pullbackCoefficientTransition Y b F)
    (pullbackCoefficientTransition_id Y b F)
    (pullbackCoefficientTransition_comp Y b F)

/-- The inverse transition is literally the original triangle identification. -/
@[simp]
theorem diagramInverseTransition_pullbackCoefficientSystem {i j : I} (a : i ⟶ j) :
    diagramInverseTransition Y (pullbackCoefficientSystem Y b F) a =
      pullbackCoefficientTransition Y b F a :=
  Equiv.symm_apply_apply _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
