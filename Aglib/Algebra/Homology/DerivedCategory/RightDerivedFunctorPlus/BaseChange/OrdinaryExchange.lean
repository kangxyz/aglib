/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherComparisons
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionTransport
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctorPlus

/-!
# Ordinary higher exchange from the original resolution formula

The component is constructed using the native ordinary right-derived functors,
the original termwise square and the native exact-functor resolution lift.
It contains no derived-category choice. For any selected derived categories,
the existing resolution formula identifies the actual transported derived
exchange with this same component by cancellation of a resolution isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] (α : R₁ ⋙ G ⟶ H ⋙ R₂)

/-- The original resolution-homology formula, with its native target comparison canceled. -/
def resolutionHigherExchangeApp {M : B} (I : InjectiveResolution M)
    (J : InjectiveResolution (H.obj M))
    (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus) (q : ℕ) :
    G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M) :=
  (G.map (I.isoRightDerivedObjCochain R₁ q).hom ≫
    (G.mapCochainComplexPlusHomologyIso (q : ℤ)).inv.app
      (R₁.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
    homologyMap
      (((exchangeOnComplexes R₁ R₂ G H α).app I.cochainComplexPlus ≫
        R₂.mapCochainComplexPlus.map φ).hom) (q : ℤ)) ≫
    (J.isoRightDerivedObjCochain R₂ q).inv

/-- The already-proved resolution equation determines the original higher arrow uniquely. -/
theorem eq_resolutionHigherExchangeApp {M : B} (I : InjectiveResolution M)
    (J : InjectiveResolution (H.obj M))
    (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus) (q : ℕ)
    (b : G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M))
    (hb : HigherResolutionExchangeEquation R₁ R₂ G H α I J φ q b) :
    b = resolutionHigherExchangeApp R₁ R₂ G H α I J φ q :=
  (Iso.eq_comp_inv (J.isoRightDerivedObjCochain R₂ q)).mpr hb

variable [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- Ordinary higher exchange uses only the original native ordinary resolutions and exact lift. -/
def ordinaryHigherExchangeApp (M : B) (q : ℕ) :
    G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M) :=
  resolutionHigherExchangeApp R₁ R₂ G H α (injectiveResolution M)
    (injectiveResolution (H.obj M))
    (InjectiveResolution.ExactFunctor.liftPlus H (injectiveResolution M)
      (injectiveResolution (H.obj M)) (𝟙 _)) q

variable [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [H.PreservesHomology]
  (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
    H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)

/-- An actual transported higher map is the intrinsic ordinary component.
Its original comparison values and defining equation are supplied before
specialization, so the conclusion keeps that actual map rather than rebuilding it. -/
theorem higherExchangeTransport_app_eq_ordinary (q : ℕ)
    (r₁ : R₁.rightDerived q ≅ DerivedCategory.Plus.singleFunctor B 0 ⋙
      R₁.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A (q : ℤ))
    (r₂ : R₂.rightDerived q ≅ DerivedCategory.Plus.singleFunctor D 0 ⋙
      R₂.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (q : ℤ))
    (hr₁ : r₁ = R₁.rightDerivedSingleHomologyIso q)
    (hr₂ : r₂ = R₂.rightDerivedSingleHomologyIso q)
    (s : R₁.rightDerived q ⋙ G ⟶ DerivedCategory.Plus.singleFunctor B 0 ⋙
      (R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C (q : ℤ))
    (t : DerivedCategory.Plus.singleFunctor B 0 ⋙
      (H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C (q : ℤ) ⟶ H ⋙ R₂.rightDerived q)
    (b : R₁.rightDerived q ⋙ G ⟶ H ⋙ R₂.rightDerived q)
    (hb : b = s ≫ whiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
      (whiskerRight β (DerivedCategory.Plus.homologyFunctor C (q : ℤ))) ≫ t)
    (hunit : ∀ K, ActualDerivedUnitEquation R₁ R₂ G H α β K)
    (hs : ∀ M, s.app M = G.map (r₁.hom.app M) ≫
      (G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
        (R₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M)))
    (ht : ∀ M, t.app M =
      (DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
        (R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
      r₂.inv.app (H.obj M)) (M : B) :
    b.app M = ordinaryHigherExchangeApp R₁ R₂ G H α M q := by
  let I := injectiveResolution M
  let J := injectiveResolution (H.obj M)
  let φ := InjectiveResolution.ExactFunctor.liftPlus H I J (𝟙 _)
  have hφ : H.mapCochainComplexPlus.map I.ιPlus ≫ φ =
      (show H.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus B 0).obj M) ⟶
          (CochainComplex.singleFunctorPlus D 0).obj (H.obj M) from
        ObjectProperty.homMk ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app M)) ≫
      J.ιPlus := by
    simpa only [Functor.map_id, Category.id_comp] using
      InjectiveResolution.ExactFunctor.liftPlus_augmentation H I J (𝟙 _)
  have hres := resolutionExchangeEquation_of_actualUnit R₁ R₂ G H α β I J φ hunit hφ
  have hcomp := whiskeredTransportEquation s β t M
    (G.map (r₁.hom.app M))
    ((G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
      (R₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M)))
    ((DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
      (R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)))
    (r₂.inv.app (H.obj M)) (hs M) (ht M)
  have hq := higherResolutionExchangeEquation_of_actualTransport R₁ R₂ G H α β I J φ q
    r₁ r₂ hr₁ hr₂ s t b hb hres hcomp
  exact eq_resolutionHigherExchangeApp R₁ R₂ G H α I J φ q _ hq

end CategoryTheory.Functor
