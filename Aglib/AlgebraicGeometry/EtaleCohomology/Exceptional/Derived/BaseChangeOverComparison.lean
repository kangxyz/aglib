/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence

/-! # Original exchange pasting normalized by actual structural triangles -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wC wD wS wC' wD' wS'

variable (Λ : Type (u + 1)) [Ring Λ]
  {C D S C' D' S' : Scheme.{u}}
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]
  [HasDerivedCategory.{wD'} (ModuleSheaf D' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]

/-- Original vertical exchange pasting in the structural-triangle normalization.
No properness or invertibility of any exchange map is used. -/
theorem moduleDerivedBaseChangeMap_over_comp
    (pC : C ⟶ S) (pD : D ⟶ S) (a : C ⟶ D) (ha : a ≫ pD = pC)
    (pC' : C' ⟶ S') (pD' : D' ⟶ S') (a' : C' ⟶ D') (ha' : a' ≫ pD' = pC')
    (b : S' ⟶ S) (qC : C' ⟶ C) (qD : D' ⟶ D)
    (hC : pC' ≫ b = qC ≫ pC) (hD : pD' ≫ b = qD ≫ pD)
    (hA : a' ≫ qD = qC ≫ a) (M : DerivedCategory.Plus (ModuleSheaf C Λ)) :
    (moduleDerivedInverseImage Λ b).map
        ((moduleDerivedDirectImageOverIso Λ pC pD a ha).hom.app M) ≫
      (moduleDerivedBaseChangeMap Λ pC pC' b qC hC).app M ≫
      (moduleDerivedDirectImageOverIso Λ pC' pD' a' ha').inv.app
        ((moduleDerivedInverseImage Λ qC).obj M) =
    (moduleDerivedBaseChangeMap Λ pD pD' b qD hD).app
        ((moduleDerivedDirectImage Λ a).obj M) ≫
      (moduleDerivedDirectImage Λ pD').map
        ((moduleDerivedBaseChangeMap Λ a a' qD qC hA).app M) := by
  subst pC
  subst pC'
  have hp := moduleDerivedBaseChangeMap_vComp Λ pD a pD' a' b qD qC hD hA hC M
  have hn := congrArg (fun z =>
    (moduleDerivedInverseImage Λ b).map
      ((moduleDerivedDirectImageCompIso Λ pD a).inv.app M) ≫ z) hp
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hn
  rw [(moduleDerivedInverseImage Λ b).map_id
    ((moduleDerivedDirectImage Λ a ⋙ moduleDerivedDirectImage Λ pD).obj M)] at hn
  simpa only [moduleDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl,
    Iso.symm_hom, Iso.symm_inv, ← Category.assoc, Category.id_comp] using hn.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
