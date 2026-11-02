/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetUnit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition

/-! # Original derived comparisons under a change of target model -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor

section General
variable {C D H₀ H₁ : Type*}
  [Category* C] [Category* D] [Category* H₀] [Category* H₁]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (T : H₀ ≌ H₁) {F : C ⥤ H₀} (R : D ⥤ H₀) (α : F ⟶ L ⋙ R)
  [R.IsRightDerivedFunctor α W]

include W in
/-- Extensionality after canonical target-equivalence transport uses the original unit. -/
theorem rightDerivedTarget_ext {G : D ⥤ H₁} (φ ψ : R ⋙ T.functor ⟶ G)
    (h : ∀ K, T.functor.map (α.app K) ≫ φ.app (L.obj K) =
      T.functor.map (α.app K) ≫ ψ.app (L.obj K)) : φ = ψ := by
  apply (R ⋙ T.functor).rightDerived_ext (rightDerivedTargetUnit L T R α) W G φ ψ
  apply NatTrans.ext
  funext K
  simpa only [rightDerivedTargetUnit, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, Category.comp_id] using h K
end General

universe u v u' v' u'' v'' dA dB dC₀ dC₁
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B] [EnoughInjectives A]
  (hA : HasDerivedCategory.{dA} A)
  (hB₀ : HasDerivedCategory.{dC₀} B) (hB₁ : HasDerivedCategory.{dC₁} B)
  (F : A ⥤ B) [F.Additive]

/-- The original derived comparison of additive functors with explicit native models. -/
abbrev rightDerivedFunctorPlusIsoModel {G : A ⥤ B} [G.Additive] (e : F ≅ G) :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _) ≅
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ G _ _) :=
  @rightDerivedFunctorPlusIso A _ _ hA _ B _ _ hB₀ F _ G _ e

/-- Original unit equation in explicitly supplied source and target models. -/
theorem rightDerivedFunctorPlusIsoModel_unit {G : A ⥤ B} [G.Additive]
    (e : F ≅ G) (K : CochainComplex.Plus A) :
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ F _ _)).app K ≫
        (rightDerivedFunctorPlusIsoModel hA hB₀ F e).hom.app (((@DerivedCategory.Plus.Q _ _ _
          hA)).obj K) =
      ((@DerivedCategory.Plus.Q _ _ _ hB₀)).map ((NatIso.mapCochainComplexPlus e).hom.app K) ≫
        ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ G _ _)).app K := by
  let := hA
  let := hB₀
  exact rightDerivedFunctorPlusIso_hom_app F e K

/-- Target transport commutes with the original derived functor-isomorphism map. -/
theorem rightDerivedFunctorPlusChangeTarget_iso {G : A ⥤ B} [G.Additive] (e : F ≅ G) :
    isoWhiskerRight (rightDerivedFunctorPlusIsoModel hA hB₀ F e)
        (canonicalEquivalence hB₀ hB₁).functor ≪≫
      rightDerivedFunctorPlusChangeTarget hA hB₀ hB₁ G =
    rightDerivedFunctorPlusChangeTarget hA hB₀ hB₁ F ≪≫
      rightDerivedFunctorPlusIsoModel hA hB₁ F e := by
  apply Iso.ext
  apply rightDerivedTarget_ext ((@DerivedCategory.Plus.Q _ _ _ hA)) (CochainComplex.Plus.quasiIso A)
    (canonicalEquivalence hB₀ hB₁) ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _))
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ F _ _))
  intro K
  dsimp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app]
  rw [← Category.assoc, ← Functor.map_comp, rightDerivedFunctorPlusIsoModel_unit,
    Functor.map_comp, Category.assoc, rightDerivedFunctorPlusChangeTarget_unit]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusChangeTarget_unit, Category.assoc,
      rightDerivedFunctorPlusIsoModel_unit]
  simpa only [comp_map, Category.assoc] using congrArg
    (fun z => z ≫ ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₁ G _ _)).app K)
    ((quotientCompCanonicalEquivalenceIso hB₀ hB₁).hom.naturality
      ((NatIso.mapCochainComplexPlus e).hom.app K))

end CategoryTheory.Functor
