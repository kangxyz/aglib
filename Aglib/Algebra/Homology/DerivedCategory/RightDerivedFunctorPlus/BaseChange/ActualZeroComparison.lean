/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison

/-! # Actual-map boundary for native degree-zero comparison

Canonical equalities identify the supplied actual maps and comparison isomorphisms.
Their substitutions occur in the generic category, before concrete specialization.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄
namespace CategoryTheory.Functor
section Exchange
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits R₁] [PreservesFiniteLimits R₂]
  [G.PreservesHomology] [H.PreservesHomology]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)
  (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
    H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)

/-- The actual original unit equation with both natural transformations explicit. -/
def ActualDerivedUnitEquation (K : CochainComplex.Plus B) : Prop :=
  G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
    β.app (DerivedCategory.Plus.Q.obj K) ≫
    R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
  G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K) ≫
    DerivedCategory.Plus.Q.map ((exchangeOnComplexes R₁ R₂ G H α).app K) ≫
    R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K)

/-- All concrete aliases enter as opaque parameters with explicit canonical witnesses.
Only this generic proof substitutes those witnesses. -/
theorem higherExchangeZero_normalization_actual
    (r₁ : R₁.rightDerived 0 ≅ DerivedCategory.Plus.singleFunctor B 0 ⋙
      R₁.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A 0)
    (r₂ : R₂.rightDerived 0 ≅ DerivedCategory.Plus.singleFunctor D 0 ⋙
      R₂.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C 0)
    (hr₁ : r₁ = R₁.rightDerivedSingleHomologyIso 0)
    (hr₂ : r₂ = R₂.rightDerivedSingleHomologyIso 0)
    (s : R₁.rightDerived 0 ⋙ G ⟶ DerivedCategory.Plus.singleFunctor B 0 ⋙
      (R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C 0)
    (t : DerivedCategory.Plus.singleFunctor B 0 ⋙
      (H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C 0 ⟶ H ⋙ R₂.rightDerived 0)
    (β₀ : R₁.rightDerived 0 ⋙ G ⟶ H ⋙ R₂.rightDerived 0)
    (hβ₀ : β₀ = s ≫ Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
      (Functor.whiskerRight β (DerivedCategory.Plus.homologyFunctor C 0)) ≫ t)
    (M : B)
    (hunit : ∀ K, ActualDerivedUnitEquation R₁ R₂ G H α β K)
    (htransport : WhiskeredTransportEquation s β t M
      (G.map (r₁.hom.app M))
      ((G.rightDerivedFunctorPlusHomologyIso 0).inv.app
        (R₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M)))
      ((DerivedCategory.Plus.homologyFunctor C 0).map
        (R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)))
      (r₂.inv.app (H.obj M))) :
    HigherExchangeZeroEquation R₁ R₂ G H α M (β₀.app M) := by
  subst r₁
  subst r₂
  subst β₀
  apply higherExchangeZero_normalization_of_eq R₁ R₂ G H α β M _
  · exact htransport.symm
  · exact hunit

end Exchange
end CategoryTheory.Functor

namespace CategoryTheory

open TwoSquare

universe uA vA wA uB vB wB uC vC wC uD vD wD
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  [EnoughInjectives D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  [G.Additive] [H.Additive] [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  [PreservesFiniteLimits R₁] [PreservesFiniteLimits R₂]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  (α : TwoSquare G L₁ L₂ H)
  (αD : TwoSquare G.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
    L₂.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)

omit [PreservesFiniteLimits R₁] [PreservesFiniteLimits R₂] in
/-- Preserve actual-map aliases at the concrete unit boundary. -/
theorem actualDerivedUnitEquation_of_mate
    (a : R₁ ⋙ G ⟶ H ⋙ R₂)
    (b : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
      H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)
    (ha : a = (mateEquiv adj₁ adj₂ α).natTrans)
    (hb : b = (mateEquiv adj₁.rightDerivedFunctorPlus
      adj₂.rightDerivedFunctorPlus αD).natTrans)
    (K : CochainComplex.Plus B)
    (hu : DerivedMateUnitEquation adj₁ adj₂ α αD K) :
    Functor.ActualDerivedUnitEquation R₁ R₂ G H a b K := by
  subst a
  subst b
  exact hu

end CategoryTheory
