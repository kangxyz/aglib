/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Original constant-sheaf unit under coefficient composition

The normalization is proved before specializing any geometric section carriers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

namespace CategoryTheory

variable {C D B : Type*} [Category* C] [Category* D] [Category* B]
  (J : GrothendieckTopology C) [HasWeakSheafify J D] [HasWeakSheafify J B]
  (F : D ⥤ B) [J.PreservesSheafification F] [J.HasSheafCompose F]

/-- The original constant-composition isomorphism preserves the original unit. -/
theorem constantCommuteCompose_toSheafify (A : D) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) F ≫
      ((constantCommuteCompose J F).hom.app A).hom =
    (Functor.constComp Cᵒᵖ A F).hom ≫
      toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc, sheafComposeIso_inv_fac,
    ← toSheafify_naturality]

/-- At an actual terminal object, coefficient composition preserves the original
constant-sheaf adjunction unit. -/
theorem constantSheafAdj_unit_w {T : C} (hT : Limits.IsTerminal T) (A : D) :
    F.map ((constantSheafAdj J D hT).unit.app A) ≫
      ((constantCommuteCompose J F).hom.app A).hom.app (op T) =
        (constantSheafAdj J B hT).unit.app (F.obj A) := by
  simp only [constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Category.id_comp]
  change F.map ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op T)) ≫
      ((constantCommuteCompose J F).hom.app A).hom.app (op T) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj A))).app (op T)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.constComp_hom_app,
    Category.id_comp] using
      NatTrans.congr_app (constantCommuteCompose_toSheafify J F A) (op T)

/-- A coefficient functor reflecting isomorphisms detects invertibility of the
original constant-sheaf unit through its original constant comparison. -/
theorem constantSheafAdj_unit_isIso_of_compose [F.ReflectsIsomorphisms]
    {T : C} (hT : Limits.IsTerminal T) (A : D)
    [IsIso ((constantSheafAdj J B hT).unit.app (F.obj A))] :
    IsIso ((constantSheafAdj J D hT).unit.app A) := by
  let η := (constantSheafAdj J D hT).unit.app A
  let e := ((sheafSections J B).obj (op T)).mapIso ((constantCommuteCompose J F).app A)
  have hcomp : IsIso (F.map η ≫ e.hom) := by
    change IsIso (F.map ((constantSheafAdj J D hT).unit.app A) ≫
      ((constantCommuteCompose J F).hom.app A).hom.app (op T))
    rw [constantSheafAdj_unit_w J F hT A]
    infer_instance
  have : IsIso (F.map η) := IsIso.of_isIso_comp_right _ e.hom
  exact isIso_of_reflects_iso η F

end CategoryTheory
