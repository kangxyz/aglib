/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.SmallModel.Functor
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Serre localization on chosen small models

An additive Serre localization preserving finite limits and finite colimits remains the
localization by its actual kernel after conjugation by the chosen small-model equivalences.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Localization/SmallModel.lean`.
SHA-256: `6fb9558471ad505fef53de335dbd70f8f9d660680b9fc3368023e0a57742237a`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.ExactCategory
namespace CategoryTheory.SmallModel
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : C ⥤ D)
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Actual Serre localization remains actual Serre localization after shrinking. -/
instance functor_isLocalization [F.IsLocalization F.kernel.isoModSerre] :
    (functor F).IsLocalization (functor F).kernel.isoModSerre := by
  let L := F ⋙ (equivSmallModel.{w} D).functor
  have hinv : (functor F).kernel.isoModSerre.IsInvertedBy (functor F) := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro X Y f hf
    exact hf
  apply Functor.IsLocalization.of_equivalence_source L F.kernel.isoModSerre
    (functor F) (functor F).kernel.isoModSerre (equivSmallModel C)
    ?_ hinv (comparison F)
  have hi : F.kernel.isoModSerre.IsInvertedBy ((equivSmallModel C).functor ⋙ functor F) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ (comparison F)).2
      (Localization.inverts L F.kernel.isoModSerre)
  intro X Y f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

end CategoryTheory.SmallModel
