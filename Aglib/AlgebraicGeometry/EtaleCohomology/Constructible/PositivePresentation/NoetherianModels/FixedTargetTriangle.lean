/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.HomLifts

/-! # Original fixed-target triangle and unit calculations

Equality transport and the adjunction calculation are performed for abstract
functor families before specializing to the actual inverse-image triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels.FixedTargetTriangle

universe u

attribute [local instance] hasSheafifyLarge

open Continuity

/-- Naturality of the actual adjunction unit, at nested functor-map heads. -/
theorem homEquiv_map_unit {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A B : C} (f : A ⟶ B) :
    adj.homEquiv _ _ (L.map f) = f ≫ adj.unit.app B := by
  change adj.unit.app A ≫ R.map (L.map f) = f ≫ adj.unit.app B
  exact (adj.unit.naturality f).symm

/-- An actual inverse comparison followed by its adjoint is the original unit. -/
theorem adjoint_unit_of_iso {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A B : C}
    (e : A ≅ B) (m : L.obj A ⟶ L.obj B) (hm : m = L.map e.hom) :
    e.inv ≫ adj.homEquiv _ _ m = adj.unit.app B := by
  have h := (congrArg (adj.homEquiv _ _) hm).trans (homEquiv_map_unit adj e.hom)
  exact (congrArg (fun k => e.inv ≫ k) h).trans
    ((Category.assoc e.inv e.hom (adj.unit.app B)).symm.trans
      ((congrArg (fun k => k ≫ adj.unit.app B) e.inv_hom_id).trans (Category.id_comp _)))

/-- Keep a supplied target transport in the same original adjunction calculation. -/
theorem adjoint_unit_of_comparison {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A B : C} {K : D}
    (e : A ≅ B) (m : L.obj A ⟶ K) (t : K ⟶ L.obj B)
    (hm : m ≫ t = L.map e.hom) :
    e.inv ≫ adj.homEquiv _ _ m ≫ R.map t = adj.unit.app B := by
  exact (congrArg (fun k => e.inv ≫ k)
    (adj.homEquiv_naturality_right m t).symm).trans
      (adjoint_unit_of_iso adj e (m ≫ t) hm)

/-- Transport an identity triangle while all functor families remain abstract. -/
theorem identity_triangle_transport {C D A B : Type*}
    [Category* C] [Category* D]
    (P : A → C ⥤ D) (Q : B → C ⥤ C) (comp : A → B → A)
    (one : B) (hOne : ∀ q, comp q one = q) (e : Q one ≅ 𝟭 C)
    (T : ∀ r δ q, comp q δ = r → (P r ≅ Q δ ⋙ P q))
    (hT : ∀ q M, (T q one q (hOne q)).inv.app M = (P q).map (e.hom.app M))
    (δ : B) (hδ : δ = one) (q r : A) (h : comp q δ = r) (hr : r = q) (M : C) :
    (T r δ q h).inv.app M ≫ eqToHom (congrArg (fun a => (P a).obj M) hr) =
      (P q).map ((eqToIso (congrArg Q hδ) ≪≫ e).hom.app M) := by
  cases hr
  cases hδ
  simp only [eqToHom_refl, Category.comp_id, eqToIso_refl, Iso.refl_trans]
  exact hT _ M

/-- The fixed-endpoint form has no residual identity transport to normalize. -/
theorem identity_triangle_transport_same {C D A B : Type*}
    [Category* C] [Category* D]
    (P : A → C ⥤ D) (Q : B → C ⥤ C) (comp : A → B → A)
    (one : B) (hOne : ∀ q, comp q one = q) (e : Q one ≅ 𝟭 C)
    (T : ∀ r δ q, comp q δ = r → (P r ≅ Q δ ⋙ P q))
    (hT : ∀ q M, (T q one q (hOne q)).inv.app M = (P q).map (e.hom.app M))
    (δ : B) (hδ : δ = one) (q : A) (h : comp q δ = q) (M : C) :
    (T q δ q h).inv.app M = (P q).map ((eqToIso (congrArg Q hδ) ≪≫ e).hom.app M) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    identity_triangle_transport P Q comp one hOne e T hT δ hδ q q h rfl M

private theorem triangle_base_identity_inv {X S : Scheme.{u}} (p : S ⟶ X)
    (B : AbelianSheaf.{u, u + 1} X) :
    (pullbackTriangleIso p (𝟙 X) p (Category.comp_id p)).inv.app B =
      (inverseImage p).map ((inverseImageId X).hom.app B) := by
  let T := pullbackTriangleIso p (𝟙 X) p (Category.comp_id p)
  have h : T.hom.app B ≫ (inverseImage p).map ((inverseImageId X).hom.app B) = 𝟙 _ := by
    simpa only [triangleCoefficientMap, eqToHom_refl, Category.id_comp] using
      triangleCoefficientMap_identity (𝟙 X) rfl p B
  exact (cancel_epi (T.hom.app B)).mp ((T.hom_inv_id_app B).trans h.symm)

/-- Original triangle, original identity comparison and original adjunction unit. -/
theorem adjoint_triangle_identity {X S : Scheme.{u}}
    (δ : X ⟶ X) (hδ : δ = 𝟙 X) (q r : S ⟶ X)
    (h : q ≫ δ = r) (hr : r = q) (B : AbelianSheaf.{u, u + 1} X) :
    (eqToIso (congrArg inverseImage hδ) ≪≫ inverseImageId X).inv.app B ≫
      (inverseImageAdjunction q).homEquiv _ _
        ((pullbackTriangleIso r δ q h).inv.app B) ≫
      (directImage q).map (eqToHom (congrArg (fun f => (inverseImage f).obj B) hr)) =
        (inverseImageAdjunction q).unit.app B := by
  exact adjoint_unit_of_comparison (inverseImageAdjunction q)
    ((eqToIso (congrArg inverseImage hδ) ≪≫ inverseImageId X).app B) _ _
    (identity_triangle_transport
      (fun a : S ⟶ X => inverseImage a) (fun a : X ⟶ X => inverseImage a)
      (fun a d => a ≫ d) (𝟙 X) Category.comp_id (inverseImageId X)
      (fun r δ q h => pullbackTriangleIso r δ q h)
      triangle_base_identity_inv δ hδ q r h hr B)

/-- The same original unit calculation with literally fixed structural endpoint. -/
theorem adjoint_triangle_identity_same {X S : Scheme.{u}}
    (δ : X ⟶ X) (hδ : δ = 𝟙 X) (q : S ⟶ X)
    (h : q ≫ δ = q) (B : AbelianSheaf.{u, u + 1} X) :
    (eqToIso (congrArg inverseImage hδ) ≪≫ inverseImageId X).inv.app B ≫
      (inverseImageAdjunction q).homEquiv _ _
        ((pullbackTriangleIso q δ q h).inv.app B) =
      (inverseImageAdjunction q).unit.app B := by
  exact adjoint_unit_of_iso (inverseImageAdjunction q)
    ((eqToIso (congrArg inverseImage hδ) ≪≫ inverseImageId X).app B) _
    (identity_triangle_transport_same
      (fun a : S ⟶ X => inverseImage a) (fun a : X ⟶ X => inverseImage a)
      (fun a d => a ≫ d) (𝟙 X) Category.comp_id (inverseImageId X)
      (fun r δ q h => pullbackTriangleIso r δ q h)
      triangle_base_identity_inv δ hδ q h B)

/-- Naturality and the specified identity component fix each structural leg. -/
theorem cone_identity_leg {I C : Type*} [Category* I] [Category* C]
    (X : I ⥤ C) (i : I) (r : (Functor.const I).obj (X.obj i) ⟶ X)
    (hr : r.app i = 𝟙 (X.obj i)) {j : I} (a : i ⟶ j) : r.app j = X.map a := by
  have h : 𝟙 (X.obj i) ≫ r.app j = r.app i ≫ X.map a := r.naturality a
  exact ((Category.id_comp _).symm.trans h).trans
    ((congrArg (fun k : X.obj i ⟶ X.obj i => k ≫ X.map a) hr).trans (Category.id_comp _))

/-- The original coefficient object transported along an actual structural equality. -/
def coefficient_stage_iso {I : Type*} [Category* I] (X : I ⥤ Scheme.{u}ᵒᵖ)
    (b : Cone X) (B : AbelianSheaf.{u, u + 1} b.pt.unop) (j : I)
    (q : b.pt ⟶ X.obj j) (h : b.π.app j = q) :
    (Stalk.pullbackCoefficientSystem X b B).obj j ≅ (inverseImage q.unop).obj B :=
  eqToIso (congrArg (fun a : b.pt ⟶ X.obj j => (inverseImage a.unop).obj B) h)

/-- Compose the actual transition, point leg and target transport before specialization. -/
theorem point_composition {C : Type*} [Category* C] {A B D E F : C}
    (e : A ⟶ B) (a : B ⟶ D) (l : D ⟶ E) (t : E ⟶ F)
    (m : B ⟶ E) (v : B ⟶ F) (w : A ⟶ F)
    (ha : a ≫ l = m) (hm : m ≫ t = v) (hv : e ≫ v = w) :
    (e ≫ a) ≫ l ≫ t = w := by
  calc
    _ = e ≫ (a ≫ l) ≫ t := by simp only [Category.assoc]
    _ = e ≫ m ≫ t := congrArg (fun k => e ≫ k ≫ t) ha
    _ = e ≫ v := congrArg (fun k => e ≫ k) hm
    _ = w := hv

end NoetherianModels.FixedTargetTriangle
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
