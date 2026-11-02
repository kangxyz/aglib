/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetCoherence

/-! # Target-model coherence of the original derived composition comparison -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor

universe u v u' v' u'' v'' dA dB dC₀ dC₁
variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  (hA : HasDerivedCategory.{dA} A) (hB : HasDerivedCategory.{dB} B)
  (hC₀ : HasDerivedCategory.{dC₀} C) (hC₁ : HasDerivedCategory.{dC₁} C)
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [F.PreservesInjectiveObjects]

/-- Original injective-preserving composition in specified independent models. -/
abbrev rightDerivedFunctorPlusCompIsoModel :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ (F ⋙ G) _ _) ≅
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB F _ _) ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hC₀ G _ _) := by
  letI := hA
  letI := hB
  letI := hC₀
  exact rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G

/-- Original two-unit equation with all three native models fixed explicitly. -/
theorem rightDerivedFunctorPlusCompIsoModel_unit (K : CochainComplex.Plus A) :
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hC₀ (F ⋙ G) _ _)).app K ≫
        (rightDerivedFunctorPlusCompIsoModel hA hB hC₀ F G).hom.app (((@DerivedCategory.Plus.Q _ _
          _ hA)).obj K) =
      ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hB hC₀ G _ _)).app
        (F.mapCochainComplexPlus.obj K) ≫
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hC₀ G _ _)).map
          (((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB F _ _)).app K) := by
  let := hA
  let := hB
  let := hC₀
  exact rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app F G K

/-- The native target comparison commutes with the original injective-preserving compositor. -/
theorem rightDerivedFunctorPlusChangeTarget_comp :
    isoWhiskerRight (rightDerivedFunctorPlusCompIsoModel hA hB hC₀ F G)
        (canonicalEquivalence hC₀ hC₁).functor ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB F _ _))
        (rightDerivedFunctorPlusChangeTarget hB hC₀ hC₁ G) =
    rightDerivedFunctorPlusChangeTarget hA hC₀ hC₁ (F ⋙ G) ≪≫
      rightDerivedFunctorPlusCompIsoModel hA hB hC₁ F G := by
  apply Iso.ext
  apply rightDerivedTarget_ext ((@DerivedCategory.Plus.Q _ _ _ hA)) (CochainComplex.Plus.quasiIso A)
    (canonicalEquivalence hC₀ hC₁) ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ (F ⋙ G) _
      _))
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hC₀ (F ⋙ G) _ _))
  intro K
  dsimp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, associator_hom_app]
  rw [Category.id_comp, ← Category.assoc, ← Functor.map_comp,
    rightDerivedFunctorPlusCompIsoModel_unit, Functor.map_comp,
    Category.assoc]
  have hn := (rightDerivedFunctorPlusChangeTarget hB hC₀ hC₁ G).hom.naturality
    (((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB F _ _)).app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, rightDerivedFunctorPlusChangeTarget_unit]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusChangeTarget_unit, Category.assoc,
      rightDerivedFunctorPlusCompIsoModel_unit]
  simp only [Category.assoc]
  rfl

end CategoryTheory.Functor
