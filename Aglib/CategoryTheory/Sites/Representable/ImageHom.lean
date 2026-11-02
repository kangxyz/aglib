/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Representable.LiftedYoneda

/-! # Yoneda maps from an actual representing test

The source object belongs to the full test subcategory through its supplied
actual comparison. In the native finite-etale instance that comparison is the
identity on the original coefficient/carrier. The target need not belong to the
test subcategory. The full Hom equivalence is proved, not supplied.
-/

@[expose] public noncomputable section

open Opposite

namespace CategoryTheory.LiftedRestrictedYoneda

universe w uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (U : C) {Y Z : D} (e : F.obj U ≅ Y)

/-- The same original identity-test inverse transported by its actual test comparison. -/
def preimageOfTest (q : presheaf.{w} F Y ⟶ presheaf.{w} F Z) : Y ⟶ Z :=
  e.inv ≫ (q.app (op U) (ULift.up e.hom)).down

/-- Postcomposition followed by the original inverse recovers the original arrow. -/
theorem preimageOfTest_map (f : Y ⟶ Z) :
    preimageOfTest.{w} F U e (map.{w} F f) = f := by
  change e.inv ≫ (e.hom ≫ f) = f
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- Fullness lifts the actual test arrow; naturality then gives the whole original value. -/
theorem preimageOfTest_app [F.Full] (q : presheaf.{w} F Y ⟶ presheaf.{w} F Z)
    (V : Cᵒᵖ) (s : F.obj V.unop ⟶ Y) :
    ULift.up (s ≫ preimageOfTest.{w} F U e q) = q.app V (ULift.up s) := by
  let f : V.unop ⟶ U := F.preimage (s ≫ e.inv)
  have h := congrArg (fun k => k (ULift.up e.hom)) (q.naturality f.op)
  change q.app V (ULift.up (F.map f ≫ e.hom)) =
    ULift.up (F.map f ≫ (q.app (op U) (ULift.up e.hom)).down) at h
  have hf : F.map f = s ≫ e.inv := F.map_preimage (s ≫ e.inv)
  rw [hf] at h
  apply ULift.ext
  have hd := congrArg (fun x : (presheaf.{w} F Z).obj V => x.down) h
  simpa only [preimageOfTest, Category.assoc, e.inv_hom_id, Category.comp_id] using hd.symm

/-- These same component values prove the second whole inverse law. -/
theorem map_preimageOfTest [F.Full] (q : presheaf.{w} F Y ⟶ presheaf.{w} F Z) :
    map.{w} F (preimageOfTest.{w} F U e q) = q := by
  ext V s
  exact preimageOfTest_app.{w} F U e q V s.down

/-- The full Hom equivalence uses the original source test and its actual comparison. -/
def homEquivOfTest [F.Full] : (Y ⟶ Z) ≃ (presheaf.{w} F Y ⟶ presheaf.{w} F Z) where
  toFun := map.{w} F
  invFun := preimageOfTest.{w} F U e
  left_inv := preimageOfTest_map.{w} F U e
  right_inv := map_preimageOfTest.{w} F U e

end CategoryTheory.LiftedRestrictedYoneda
