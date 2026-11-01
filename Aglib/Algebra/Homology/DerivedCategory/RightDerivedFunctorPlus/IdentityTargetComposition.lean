/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.IdentityModelComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetCoherence

/-! # Original composition with an identity functor across independent target models -/
@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor
universe u v u' v' dA dB₀ dB₁
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
  (hA : HasDerivedCategory.{dA} A)
  (hB₀ : HasDerivedCategory.{dB₀} B) (hB₁ : HasDerivedCategory.{dB₁} B)
  (F : A ⥤ B) (I : B ⥤ B) [F.Additive] [I.Additive] [I.PreservesHomology]
  (e : I ≅ 𝟭 B)

/-- The original exact-second compositor, with its three native models explicit. -/
abbrev rightDerivedFunctorPlusExactCompIsoModel :
    (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₁ (F ⋙ I) _ _) ≅
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _) ⋙
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hB₀ hB₁ I _ _) :=
  @rightDerivedFunctorPlusCompIsoOfPreservesHomology A _ _ hA _ B _ _ hB₀ F _
    B _ _ hB₁ _ I _ _

/-- The original two-unit formula with independent middle and target models. -/
theorem rightDerivedFunctorPlusExactCompIsoModel_unit (K : CochainComplex.Plus A) :
    (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₁ (F ⋙ I) _ _).app K ≫
      (rightDerivedFunctorPlusExactCompIsoModel hA hB₀ hB₁ F I).hom.app
        ((@DerivedCategory.Plus.Q _ _ _ hA).obj K) =
    (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hB₀ hB₁ I _ _).app (F.mapCochainComplexPlus.obj K) ≫
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hB₀ hB₁ I _ _).map
        ((@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ F _ _).app K) :=
  @rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app A _ _ hA _ B _ _ hB₀ F _
    B _ _ hB₁ _ I _ _ K

/-- Actual composition with the identity-derived functor is canonical target transport,
with the original ordinary contraction and original derived unit retained. -/
theorem rightDerivedFunctorPlus_identityTargetComposition :
    rightDerivedFunctorPlusExactCompIsoModel hA hB₀ hB₁ F I ≪≫
      isoWhiskerLeft (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _)
        (rightDerivedFunctorPlusIdentityModelIso hB₀ hB₁ I e) ≪≫
      rightDerivedFunctorPlusChangeTarget hA hB₀ hB₁ F =
    (@rightDerivedFunctorPlusIso _ _ _ hA _ _ _ _ hB₁ (F ⋙ I) _ _ _
      (isoWhiskerLeft F e ≪≫ rightUnitor F)) := by
  let := hA
  let := hB₀
  let := hB₁
  apply Iso.ext
  apply (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₁ (F ⋙ I) _ _).rightDerived_ext
    (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₁ (F ⋙ I) _ _)
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom, isoWhiskerLeft_hom]
  rw [← Category.assoc, ← Category.assoc,
    rightDerivedFunctorPlusExactCompIsoModel_unit]
  have hn := (rightDerivedFunctorPlusIdentityModelIso hB₀ hB₁ I e).hom.naturality
    ((@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ F _ _).app K)
  simp only [comp_obj] at hn
  simp only [Category.assoc]
  rw [← Category.assoc ((@rightDerivedFunctorPlus _ _ _ _ _ _ hB₀ hB₁ I _ _).map _), hn]
  simp only [Category.assoc]
  have hi := rightDerivedFunctorPlusIdentityModelIso_unit hB₀ hB₁ I e
    (F.mapCochainComplexPlus.obj K)
  have ht := rightDerivedFunctorPlusChangeTarget_unit hA hB₀ hB₁ F K
  rw [ht]
  have hi' := congrArg (fun z => z ≫
    (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₁ F _ _).app K) hi
  simp only [Category.assoc] at hi'
  rw [hi']
  rw [rightDerivedFunctorPlusIso_hom_app]
  congr 1

end CategoryTheory.Functor
