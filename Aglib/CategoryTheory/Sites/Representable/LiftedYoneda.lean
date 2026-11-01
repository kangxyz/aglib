/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! # The actual lifted Yoneda realization on a full test subcategory

The inverse of a natural map is evaluation at the identity section. Fullness
of the test inclusion proves the other inverse law on every original test.
The Hom and Iso constructions use these same maps, also when the represented
presheaves are supplied with their actual sheafhood proofs. No desired
full-faithfulness or comparison is supplied as a premise.
-/

@[expose] public noncomputable section

open Opposite

namespace CategoryTheory.LiftedRestrictedYoneda

universe w uC vC uD vD

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D)

/-- The original restricted representable with its one necessary value lift. -/
def presheaf (Y : D) : Cᵒᵖ ⥤ Type (max vD w) :=
  F.op ⋙ yoneda.obj Y ⋙ uliftFunctor.{w}

/-- Actual postcomposition on the same lifted sections. -/
def map {Y Z : D} (f : Y ⟶ Z) : presheaf.{w} F Y ⟶ presheaf.{w} F Z where
  app U := ↾fun s => ULift.up (s.down ≫ f)
  naturality {U V} g := by
    ext s
    exact congrArg ULift.up (Category.assoc _ _ _)

@[simp] theorem map_app {Y Z : D} (f : Y ⟶ Z) (U : Cᵒᵖ)
    (s : (presheaf.{w} F Y).obj U) :
    (map.{w} F f).app U s = ULift.up (s.down ≫ f) := rfl

@[simp] theorem map_id (Y : D) : map.{w} F (𝟙 Y) = 𝟙 (presheaf.{w} F Y) := by
  ext U s
  exact congrArg ULift.up (Category.comp_id s.down)

theorem map_comp {Y Z W : D} (f : Y ⟶ Z) (g : Z ⟶ W) :
    map.{w} F (f ≫ g) = map.{w} F f ≫ map.{w} F g := by
  ext U s
  exact congrArg ULift.up (Category.assoc _ _ _).symm

/-- The actual inverse evaluates on the identity of the represented test. -/
def preimage {Y Z : C}
    (q : presheaf.{w} F (F.obj Y) ⟶ presheaf.{w} F (F.obj Z)) : F.obj Y ⟶ F.obj Z :=
  (q.app (op Y) (ULift.up (𝟙 (F.obj Y)))).down

@[simp] theorem preimage_map {Y Z : C} (f : F.obj Y ⟶ F.obj Z) :
    preimage.{w} F (map.{w} F f) = f := Category.id_comp f

/-- Naturality at the actual preimage of a test arrow proves every component. -/
theorem map_preimage [F.Full] {Y Z : C}
    (q : presheaf.{w} F (F.obj Y) ⟶ presheaf.{w} F (F.obj Z)) :
    map.{w} F (preimage.{w} F q) = q := by
  ext U s
  let f : U.unop ⟶ Y := F.preimage s.down
  have h := congrArg (fun k => k (ULift.up (𝟙 (F.obj Y)))) (q.naturality f.op)
  change q.app U (ULift.up (F.map f ≫ 𝟙 (F.obj Y))) =
    ULift.up (F.map f ≫ preimage.{w} F q) at h
  have hf : F.map f = s.down := F.map_preimage s.down
  rw [hf, Category.comp_id] at h
  exact h.symm

/-- The whole Hom equivalence is proved from the original two maps. -/
def homEquiv [F.Full] (Y Z : C) :
    (F.obj Y ⟶ F.obj Z) ≃
      (presheaf.{w} F (F.obj Y) ⟶ presheaf.{w} F (F.obj Z)) where
  toFun := map.{w} F
  invFun := preimage.{w} F
  left_inv := preimage_map.{w} F
  right_inv := map_preimage.{w} F

/-- Recovering a morphism retains its exact original section value. -/
theorem preimage_app [F.Full] {Y Z : C}
    (q : presheaf.{w} F (F.obj Y) ⟶ presheaf.{w} F (F.obj Z))
    (U : Cᵒᵖ) (s : F.obj U.unop ⟶ F.obj Y) :
    ULift.up (s ≫ preimage.{w} F q) = q.app U (ULift.up s) :=
  congrArg (fun r => r.app U (ULift.up s)) (map_preimage.{w} F q)

/-- Postcomposition sends an actual isomorphism to the same component maps. -/
def mapIso {Y Z : D} (e : Y ≅ Z) : presheaf.{w} F Y ≅ presheaf.{w} F Z where
  hom := map.{w} F e.hom
  inv := map.{w} F e.inv
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

/-- The whole inverse isomorphism uses the same identity-section preimages. -/
def preimageIso [F.Full] {Y Z : C}
    (e : presheaf.{w} F (F.obj Y) ≅ presheaf.{w} F (F.obj Z)) : F.obj Y ≅ F.obj Z where
  hom := preimage.{w} F e.hom
  inv := preimage.{w} F e.inv
  hom_inv_id := by
    apply (homEquiv.{w} F Y Y).injective
    change map.{w} F (_ ≫ _) = map.{w} F (𝟙 _)
    rw [map_comp, map_preimage, map_preimage, map_id]
    exact e.hom_inv_id
  inv_hom_id := by
    apply (homEquiv.{w} F Z Z).injective
    change map.{w} F (_ ≫ _) = map.{w} F (𝟙 _)
    rw [map_comp, map_preimage, map_preimage, map_id]
    exact e.inv_hom_id

section Sheaves

variable (J : GrothendieckTopology C)

/-- The same represented presheaf with its supplied actual sheafhood proof. -/
def sheaf (Y : D) (hY : Presheaf.IsSheaf J (presheaf.{w} F Y)) :
    Sheaf J (Type (max vD w)) := ⟨presheaf.{w} F Y, hY⟩

/-- Postcomposition is a sheaf map on the original represented sheaves. -/
def sheafMap {Y Z : D} (hY : Presheaf.IsSheaf J (presheaf.{w} F Y))
    (hZ : Presheaf.IsSheaf J (presheaf.{w} F Z)) (f : Y ⟶ Z) :
    sheaf.{w} F J Y hY ⟶ sheaf.{w} F J Z hZ := ⟨map.{w} F f⟩

/-- The complete sheaf Hom equivalence retains the original two inverse maps. -/
def sheafHomEquiv [F.Full] (Y Z : C)
    (hY : Presheaf.IsSheaf J (presheaf.{w} F (F.obj Y)))
    (hZ : Presheaf.IsSheaf J (presheaf.{w} F (F.obj Z))) :
    (F.obj Y ⟶ F.obj Z) ≃
      (sheaf.{w} F J (F.obj Y) hY ⟶ sheaf.{w} F J (F.obj Z) hZ) where
  toFun := sheafMap.{w} F J hY hZ
  invFun q := preimage.{w} F q.hom
  left_inv := preimage_map.{w} F
  right_inv q := by
    apply Sheaf.hom_ext
    exact map_preimage.{w} F q.hom

/-- The same postcomposition maps form the represented sheaf isomorphism. -/
def sheafMapIso {Y Z : D} (hY : Presheaf.IsSheaf J (presheaf.{w} F Y))
    (hZ : Presheaf.IsSheaf J (presheaf.{w} F Z)) (e : Y ≅ Z) :
    sheaf.{w} F J Y hY ≅ sheaf.{w} F J Z hZ :=
  ObjectProperty.isoMk _ (mapIso.{w} F e)

/-- The sheaf isomorphism inverse is assembled on the same represented objects. -/
def sheafPreimageIso [F.Full] {Y Z : C}
    (hY : Presheaf.IsSheaf J (presheaf.{w} F (F.obj Y)))
    (hZ : Presheaf.IsSheaf J (presheaf.{w} F (F.obj Z)))
    (e : sheaf.{w} F J (F.obj Y) hY ≅ sheaf.{w} F J (F.obj Z) hZ) : F.obj Y ≅ F.obj Z :=
  preimageIso.{w} F ((sheafToPresheaf J (Type (max vD w))).mapIso e)

end Sheaves
end CategoryTheory.LiftedRestrictedYoneda
