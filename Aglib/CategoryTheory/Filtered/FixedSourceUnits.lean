/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Filtered.SystemConstructions
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeRightTail
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeExtension

/-! # Actual fixed-source triangle units

The original identity and triangle comparisons normalize the fixed-source
adjunction units. These are equations for the given adjunctions, with no
replacement coefficient category or fullness hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem.AdjunctionData

variable {J : Type*} [Category* J] {A : J → Type*} [∀ j, Category* (A j)]
    (D : AdjunctionData A) (hD : D.Coherent)

include hD in
/-- Original identity triangles have the inverse value dictated by the
actual left identity comparison. -/
theorem identityTriangle_inv {x y : J} (q : x ⟶ y) (B : A x) :
    (D.triangleIso q (𝟙 x) q (Category.id_comp q)).inv.app B =
      (D.left q).map ((D.leftIdIso x).hom.app B) := by
  let T := D.triangleIso q (𝟙 x) q (Category.id_comp q)
  have h : T.hom.app B ≫ (D.left q).map ((D.leftIdIso x).hom.app B) = 𝟙 _ := by
    simpa only [triangleCoefficientMap, eqToHom_refl, Category.id_comp] using
      D.triangleCoefficientMap_identity hD (𝟙 x) rfl q B
  exact (cancel_epi (T.hom.app B)).mp ((T.hom_inv_id_app B).trans h.symm)

include hD in
/-- The original adjunction mate of the identity-source triangle, including
its actual equality transport, is the original unit. -/
theorem fixedSourceTriangle_unit {x y : J}
    (δ : x ⟶ x) (hδ : δ = 𝟙 x) (q r : x ⟶ y)
    (h : δ ≫ q = r) (hr : r = q) (B : A x) :
    (eqToIso (congrArg D.left hδ) ≪≫ D.leftIdIso x).inv.app B ≫
      (D.adj q).homEquiv _ _ ((D.triangleIso r δ q h).inv.app B) ≫
      (D.right q).map (eqToHom (congrArg (fun f => (D.left f).obj B) hr)) =
        (D.adj q).unit.app B := by
  cases hr
  cases hδ
  simp only [eqToIso_refl, Iso.refl_trans, eqToHom_refl, Functor.map_id, Category.comp_id]
  rw [D.identityTriangle_inv hD]
  have hn := ((D.adj q).unit.naturality ((D.leftIdIso x).hom.app B)).symm
  change (D.adj q).homEquiv _ _ ((D.left q).map ((D.leftIdIso x).hom.app B)) =
    (D.leftIdIso x).hom.app B ≫ (D.adj q).unit.app B at hn
  exact (congrArg (fun k => (D.leftIdIso x).inv.app B ≫ k) hn).trans
    ((D.leftIdIso x).inv_hom_id_app_assoc B _)

/-- Structural identity components retain every actual diagram arrow. -/
theorem fixedBaseCone_leg {I : Type*} [Category* I] (X : I ⥤ J)
    (i : I) (r : (Functor.const I).obj (X.obj i) ⟶ X)
    (hr : r.app i = 𝟙 (X.obj i)) {j : I} (a : i ⟶ j) : r.app j = X.map a := by
  have h : 𝟙 (X.obj i) ≫ r.app j = r.app i ≫ X.map a := r.naturality a
  exact ((Category.id_comp _).symm.trans h).trans
    ((congrArg (fun k : X.obj i ⟶ X.obj i => k ≫ X.map a) hr).trans (Category.id_comp _))

end CategoryTheory.InjectiveSystem.AdjunctionData

namespace CategoryTheory.InjectiveSystem

/-- Composing an original system map with its right-tail transition retains
the original composite-arrow map. -/
theorem System.rightTailTransition_unit
    {J : Type*} [Category* J] {A : J → Type*} [∀ j, Category* (A j)]
    (D : AdjunctionData A) (F : System D)
    {i j k : J} (a : i ⟶ j) (b : j ⟶ k) (t : i ⟶ k) (h : a ≫ b = t)
    {P : A i} (s : P ⟶ F.obj i) :
    (s ≫ F.map a) ≫ System.rightTailTransition D F a b t h = s ≫ F.map t := by
  subst t
  simpa only [System.rightTailTransition, System.rightStep, eqToHom_refl,
    Category.comp_id, Category.assoc] using
    congrArg (fun k => s ≫ k) (System.map_comp_inv D F a b)

end CategoryTheory.InjectiveSystem
