/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdge
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! Evaluation of the original top projection and its shifted trace. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShiftedHom

variable {D : Type*} [Category* D] [HasShift D ℤ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comp_eq_mk₀_id_of_inverseShiftAdjunct
    {U K : D} (q : ℤ) (z : ShiftedHom U K q) (τ : ShiftedHom K U (-q))
    (h : (((shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction.homEquiv U K).symm z) ≫
      τ = 𝟙 (U⟦-q⟧)) :
    z.comp τ (neg_add_cancel q) = ShiftedHom.mk₀ 0 rfl (𝟙 U) := by
  let adj : shiftFunctor D (-q) ⊣ shiftFunctor D q :=
    (shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction
  let j := (adj.homEquiv U K).symm z
  have hj : adj.homEquiv U K j = z := (adj.homEquiv U K).apply_symm_apply z
  change j ≫ τ = 𝟙 (U⟦-q⟧) at h
  have he := congrArg (adj.homEquiv U (U⟦-q⟧)) h
  rw [adj.homEquiv_naturality_right, hj] at he
  have hu : z ≫ τ⟦q⟧' = adj.unit.app U := by
    rw [adj.homEquiv_unit] at he
    change z ≫ τ⟦q⟧' = adj.unit.app U ≫ (shiftFunctor D q).map (𝟙 _) at he
    rw [(shiftFunctor D q).map_id] at he
    exact he.trans (Category.comp_id (adj.unit.app U))
  rw [ShiftedHom.comp, ShiftedHom.mk₀]
  simp only [shiftFunctorZero', eqToIso_refl, Iso.refl_trans, Category.id_comp]
  rw [← Category.assoc, hu]
  have hunit : adj.unit.app U = (shiftFunctorZero D ℤ).inv.app U ≫
      (shiftFunctorAdd' D (-q) q 0 (neg_add_cancel q)).hom.app U := rfl
  rw [hunit, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end CategoryTheory.ShiftedHom

namespace DerivedCategory.Plus

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original top homology value determines the original shifted trace composite. -/
theorem shifted_topTrace_comp_eq_id_of_value
    (q : ℤ) (U : C) (K : Plus C) [K.IsLE q]
    (z : ShiftedHom ((singleFunctor C 0).obj U) K q)
    (a : (homologyFunctor C q).obj K ⟶ U)
    (hz : let I := (singleFunctor C 0).obj U
      let e := ((singleFunctors C).shiftIso (-q) q 0 (neg_add_cancel q)).app U
      let j := ((shiftEquiv' (Plus C) (-q) q (neg_add_cancel q)).toAdjunction.homEquiv I K).symm z
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app U ≫
        (homologyFunctor C q).map (e.inv ≫ j) ≫ a = 𝟙 U) :
    let e := ((singleFunctors C).shiftIso (-q) q 0 (neg_add_cancel q)).app U
    z.comp (upperHomologyProjection K q ≫ (singleFunctor C q).map a ≫ e.inv)
      (neg_add_cancel q) = ShiftedHom.mk₀ 0 rfl (𝟙 _) := by
  dsimp only at hz ⊢
  let I := (singleFunctor C 0).obj U
  let e : I⟦-q⟧ ≅ (singleFunctor C q).obj U :=
    ((singleFunctors C).shiftIso (-q) q 0 (neg_add_cancel q)).app U
  let j := ((shiftEquiv' (Plus C) (-q) q (neg_add_cancel q)).toAdjunction.homEquiv I K).symm z
  have h := upperHomologyProjection_comp_eq_id_of_value q U K (e.inv ≫ j) a hz
  apply ShiftedHom.comp_eq_mk₀_id_of_inverseShiftAdjunct
  have hc := congrArg (fun f => e.hom ≫ f ≫ e.inv) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp, Iso.hom_inv_id] at hc
  dsimp only [I, j, e] at hc
  exact hc

end DerivedCategory.Plus
