/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback

/-! # Detection of the original constant-ring pullback unit

Only the specified transport comparison and the units of the two original
coefficient equivalences are cancelled. The functor observing the unit is
arbitrary and no preservation of injectives is involved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ r w uA vA

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [K.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)]

/-- An observer detects invertibility of the same original unit before the
fixed coefficient-equivalence transport. -/
theorem moduleInverseImage_unit_map_isIso_iff
    {A : Type uA} [Category.{vA} A]
    (H : ModuleSheaf.{u₁, v₁, r, w} J Λ ⥤ A)
    (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    IsIso (H.map ((moduleInverseImageAdjunction F J K Λ).unit.app M)) ↔
      IsIso (((moduleSheafEquivalence J Λ).functor ⋙ H).map
        ((moduleValuedInverseImageAdjunction F J K Λ).unit.app
          ((moduleSheafEquivalence J Λ).inverse.obj M))) := by
  have hn : IsIso (H.map ((moduleInverseImageAdjunction F J K Λ).unit.app M)) ↔
      IsIso (H.map ((moduleTransportAdjunction F J K Λ).unit.app M)) := by
    rw [← moduleInverseImageTransportIso_unit_app F J K Λ M,
      CategoryTheory.Functor.map_comp, isIso_comp_right_iff]
  rw [hn]
  let EX := moduleSheafEquivalence J Λ
  let ES := moduleSheafEquivalence K Λ
  let adj := EX.symm.toAdjunction.comp (moduleValuedInverseImageAdjunction F J K Λ)
  change IsIso (H.map ((adj.comp ES.toAdjunction).unit.app M ≫
    (moduleDirectImageTransportIso F J K Λ).inv.app
      (((EX.inverse ⋙ moduleValuedInverseImage F J K Λ) ⋙ ES.functor).obj M))) ↔ _
  rw [CategoryTheory.Functor.map_comp, isIso_comp_right_iff,
    Adjunction.comp_unit_app, CategoryTheory.Functor.map_comp]
  let : IsIso (ES.toAdjunction.unit.app
      ((EX.inverse ⋙ moduleValuedInverseImage F J K Λ).obj M)) := by
    change IsIso (ES.unitIso.hom.app _)
    infer_instance
  rw [isIso_comp_right_iff]
  change IsIso (H.map ((EX.symm.toAdjunction.comp
    (moduleValuedInverseImageAdjunction F J K Λ)).unit.app M)) ↔ _
  rw [Adjunction.comp_unit_app, CategoryTheory.Functor.map_comp]
  let : IsIso (EX.symm.toAdjunction.unit.app M) := by
    change IsIso (EX.counitIso.inv.app M)
    infer_instance
  exact isIso_comp_left_iff _ _

end ModuleCat.Sheaf.ConstantRing
