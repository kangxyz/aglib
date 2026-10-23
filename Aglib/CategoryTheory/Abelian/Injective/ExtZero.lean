/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Degree-zero normalization for original injective-resolution Ext

Extracted unchanged from the generic private ExtZero section of
`Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology`.
The statement does not require any geometric hypotheses.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CochainComplex HomComplex

namespace CategoryTheory.InjectiveResolution

universe v w t

variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{t} C]

omit [HasExt C] in
private theorem cocycle_equivHomShift_ofHom {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom φ) = ShiftedHom.mk₀ (0 : ℤ) rfl φ := by
  ext i
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.ofHom,
    Cochain.rightShift_v, Cochain.ofHom, ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f,
    HomologicalComplex.XIsoOfEq]

/-- The original degree-zero resolution cocycle is the native degree-zero Ext class. -/
theorem extMk_ι_zero {U M : C} (I : InjectiveResolution M) (g : U ⟶ M) :
    I.extMk (g ≫ I.ι.f 0) 1 rfl (by
      rw [Category.assoc, I.ι.comm 0 1]
      simp) = Ext.mk₀ g := by
  let := HasDerivedCategory.standard C
  have h0 : (g ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, I.ι.comm 0 1]
    simp
  have hc :
      Cocycle.fromSingleMk ((g ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv)
          (zero_add (0 : ℤ)) 1 rfl (by
            rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            simpa only [Category.assoc, zero_comp] using
              congrArg (fun k => k ≫ (I.cochainComplexXIso 1 1 rfl).inv) h0) =
        Cocycle.ofHom ((CochainComplex.singleFunctor C 0).map g ≫ I.ι') := by
    apply Cocycle.ext
    apply (Cochain.fromSingleEquiv (zero_add (0 : ℤ))).injective
    simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
    dsimp only [Cocycle.ofHom, Cocycle.mk, Cochain.fromSingleEquiv]
    change _ = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 U).inv ≫
      (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map g ≫ I.ι')).v 0 0 (add_zero 0)
    rw [Cochain.ofHom_v]
    rw [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      InjectiveResolution.ι'_f_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext
  rw [InjectiveResolution.extMk_hom]
  erw [hc]
  erw [cocycle_equivHomShift_ofHom, ShiftedHom.map_mk₀,
    ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀, Ext.mk₀_hom]
  congr 1
  have hn := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality g
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]


end CategoryTheory.InjectiveResolution
