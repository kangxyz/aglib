/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualZeroComparison

/-! # Original exchange on supplied injective resolutions

The actual complex-unit equation identifies the original derived exchange with
termwise ordinary exchange followed by an augmentation-compatible map into an
actual target injective resolution. Only the exact horizontal functors' units
and original resolution inclusions are cancelled. Inverse image is not assumed
to preserve injective objects, and no cohomological comparison is a premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

section ExactResolution

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (H : B ⥤ D) [H.Additive] [H.PreservesHomology]
  {M : B} (I : InjectiveResolution M) (J : InjectiveResolution (H.obj M))
  (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus)
  (hφ : H.mapCochainComplexPlus.map I.ιPlus ≫ φ =
    (show H.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus B 0).obj M) ⟶
        (CochainComplex.singleFunctorPlus D 0).obj (H.obj M) from
      ObjectProperty.homMk ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app M)) ≫
      J.ιPlus)

include hφ in
/-- An actual resolution lift respects the installed exact-single comparison. -/
theorem rightDerivedFunctorPlusSingleIso_comp_resolution :
    (H.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
        DerivedCategory.Plus.Q.map J.ιPlus =
      H.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) ≫
        H.rightDerivedFunctorPlusExactComparison.hom.app I.cochainComplexPlus ≫
        DerivedCategory.Plus.Q.map φ := by
  let K := (CochainComplex.singleFunctorPlus B 0).obj M
  let σ : H.mapCochainComplexPlus.obj K ⟶
      (CochainComplex.singleFunctorPlus D 0).obj (H.obj M) :=
    ObjectProperty.homMk ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app M)
  have hs : (H.rightDerivedFunctorPlusSingleIso 0).hom.app M =
      H.rightDerivedFunctorPlusExactComparison.hom.app K ≫
        DerivedCategory.Plus.Q.map σ := by
    have : IsIso H.rightDerivedFunctorPlusUnit :=
      H.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    apply (cancel_epi (H.rightDerivedFunctorPlusUnit.app K)).mp
    rw [H.rightDerivedFunctorPlusSingleIso_unit]
    have hi := H.rightDerivedFunctorPlusExactComparison.inv_hom_id_app K
    change H.rightDerivedFunctorPlusUnit.app K ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app K = 𝟙 _ at hi
    rw [← Category.assoc, hi, Category.id_comp]
  have hn := H.rightDerivedFunctorPlusExactComparison.hom.naturality I.ιPlus
  simp only [Functor.comp_map] at hn
  have hq := congrArg (fun a => DerivedCategory.Plus.Q.map a) hφ
  simp only [Functor.map_comp] at hq
  rw [hs, Category.assoc, ← hq]
  simpa only [Category.assoc] using
    congrArg (fun a => a ≫ DerivedCategory.Plus.Q.map φ) hn.symm

end ExactResolution

section Exchange

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)
  (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
    H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)
  {M : B} (I : InjectiveResolution M) (J : InjectiveResolution (H.obj M))
  (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus)

/-- The literal original exchange compared with the actual resolution-complex map. -/
def ResolutionExchangeEquation : Prop :=
  G.rightDerivedFunctorPlus.map (I.rightDerivedFunctorPlusIso R₁).hom ≫
      β.app ((DerivedCategory.Plus.singleFunctor B 0).obj M) ≫
      R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M) =
    G.rightDerivedFunctorPlusExactComparison.hom.app
        (R₁.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      DerivedCategory.Plus.Q.map
        ((exchangeOnComplexes R₁ R₂ G H α).app I.cochainComplexPlus ≫
          R₂.mapCochainComplexPlus.map φ) ≫
      (J.rightDerivedFunctorPlusIso R₂).hom

/-- The actual complex-unit square determines exchange on every supplied
resolution lift. No target cohomology isomorphism or vanishing is assumed. -/
theorem resolutionExchangeEquation_of_actualUnit
    (hunit : ∀ K, ActualDerivedUnitEquation R₁ R₂ G H α β K)
    (hφ : H.mapCochainComplexPlus.map I.ιPlus ≫ φ =
      (show H.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus B 0).obj M) ⟶
          (CochainComplex.singleFunctorPlus D 0).obj (H.obj M) from
        ObjectProperty.homMk ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app M)) ≫
        J.ιPlus) :
    ResolutionExchangeEquation R₁ R₂ G H α β I J φ := by
  dsimp only [ResolutionExchangeEquation]
  apply (cancel_mono
    (R₂.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map J.ιPlus))).mp
  simp only [Category.assoc]
  rw [InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp R₂ J]
  have ht := congrArg R₂.rightDerivedFunctorPlus.map
    (rightDerivedFunctorPlusSingleIso_comp_resolution H I J φ hφ)
  simp only [Functor.map_comp] at ht
  rw [ht]
  have hn := β.naturality (DerivedCategory.Plus.Q.map I.ιPlus)
  change G.rightDerivedFunctorPlus.map
      (R₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus)) ≫
      β.app (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) =
    β.app ((DerivedCategory.Plus.singleFunctor B 0).obj M) ≫
      R₂.rightDerivedFunctorPlus.map
        (H.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus)) at hn
  rw [← reassoc_of% hn, ← G.rightDerivedFunctorPlus.map_comp_assoc,
    InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp R₁ I]
  have hu := hunit I.cochainComplexPlus
  change G.rightDerivedFunctorPlus.map
      (R₁.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus) ≫
      β.app (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) ≫
      R₂.rightDerivedFunctorPlus.map
        (H.rightDerivedFunctorPlusExactComparison.hom.app I.cochainComplexPlus) = _ at hu
  rw [reassoc_of% hu]
  have hr := R₂.rightDerivedFunctorPlusUnit.naturality φ
  simp only [Functor.comp_map] at hr
  rw [← hr]
  simp only [Functor.map_comp, Category.assoc]

end Exchange

end CategoryTheory.Functor
