/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdgeTrace
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext

/-! The original degree-zero Ext class of a shifted trace. -/

open CategoryTheory CategoryTheory.Abelian

@[expose] public noncomputable section

namespace DerivedCategory.Plus

universe u v d e

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{d} C] [HasExt.{e} C]

/-- An original shifted trace evaluates its original homology value as a degree-zero Ext class. -/
theorem eq_mk₀_of_singleShiftTrace_homPlus (q : ℤ) {U V : C} {K : Plus C}
    (x : (singleFunctor C q).obj U ⟶ K)
    (t : ShiftedHom K ((singleFunctor C 0).obj V) (-q))
    (y : Ext.{e} U V 0)
    (hy :
      let F := singleFunctor C 0
      let η := (singleFunctors C).shiftIso (-q) q 0 (by omega)
      let adj := (shiftEquiv' (Plus C) (-q) q (by omega)).toAdjunction
      let z : ShiftedHom (F.obj U) K q := adj.homEquiv (F.obj U) K (η.hom.app U ≫ x)
      y.homPlus = z.comp t (by omega : -q + q = 0)) :
    let H := homologyFunctor C q
    let E := singleFunctorCompHomologyFunctorIso (C := C) q
    let η := (singleFunctors C).shiftIso (-q) q 0 (by omega)
    y = Ext.mk₀ (E.inv.app U ≫ H.map (x ≫ t ≫ η.hom.app V) ≫ E.hom.app V) := by
  intro H E η
  let F := singleFunctor C 0
  let adj := (shiftEquiv' (Plus C) (-q) q (by omega)).toAdjunction
  let z : ShiftedHom (F.obj U) K q := adj.homEquiv (F.obj U) K (η.hom.app U ≫ x)
  let a := E.inv.app U ≫ H.map (x ≫ t ≫ η.hom.app V) ≫ E.hom.app V
  let μ := shiftFunctorCompIsoId (Plus C) (-q) q (by omega)
  let b := z ≫ t⟦q⟧' ≫ μ.hom.app (F.obj V)
  have h₁ : z.comp t (by omega : -q + q = 0) = ShiftedHom.mk₀ 0 rfl b :=
    ShiftedHom.comp_neg_eq_mk₀ q z t
  have h₂ : b = F.map a := singleShiftTrace_homology_value q x t
  apply Ext.homPlus_injective 0
  exact hy.trans (h₁.trans ((congrArg (ShiftedHom.mk₀ 0 rfl) h₂).trans
    (Ext.homPlus_mk₀ a).symm))

/-- The degree-zero trace uses the supplied value of the original homology map. -/
theorem eq_mk₀_of_singleShiftTrace_homologyValue (q : ℤ) {U V : C} {K : Plus C}
    (x : (singleFunctor C q).obj U ⟶ K)
    (t : ShiftedHom K ((singleFunctor C 0).obj V) (-q))
    (a : U ⟶ (homologyFunctor C q).obj K)
    (hx : (homologyFunctor C q).map x =
      (singleFunctorCompHomologyFunctorIso (C := C) q).hom.app U ≫ a)
    (y : Ext.{e} U V 0)
    (hy :
      let F := singleFunctor C 0
      let η := (singleFunctors C).shiftIso (-q) q 0 (by omega)
      let adj := (shiftEquiv' (Plus C) (-q) q (by omega)).toAdjunction
      let z : ShiftedHom (F.obj U) K q := adj.homEquiv (F.obj U) K (η.hom.app U ≫ x)
      y.homPlus = z.comp t (by omega : -q + q = 0)) :
    let H := homologyFunctor C q
    let E := singleFunctorCompHomologyFunctorIso (C := C) q
    let η := (singleFunctors C).shiftIso (-q) q 0 (by omega)
    y = Ext.mk₀ (a ≫ H.map (t ≫ η.hom.app V) ≫ E.hom.app V) := by
  intro H E η
  have h := eq_mk₀_of_singleShiftTrace_homPlus q x t y hy
  dsimp only at h
  change y = Ext.mk₀ (E.inv.app U ≫ H.map (x ≫ t ≫ η.hom.app V) ≫ E.hom.app V) at h
  have hm := H.map_comp x (t ≫ η.hom.app V)
  rw [hm, hx] at h
  change y = Ext.mk₀ (E.inv.app U ≫ ((E.hom.app U ≫ a) ≫
    H.map (t ≫ η.hom.app V)) ≫ E.hom.app V) at h
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using h

end DerivedCategory.Plus
