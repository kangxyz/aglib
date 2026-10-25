/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionHomology

/-! # Actual-map transport boundary for resolution exchange

The original source and target comparison aliases and the original higher
natural transformation enter explicitly. Their defining equalities are
substituted before concrete functors are supplied. The result is the same
original resolution-homology equation, not a second comparison map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

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
  (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus) (q : ℕ)

/-- Actual aliases retain the already proved transport equation at its shared
head until all substitutions have occurred in the generic category. -/
theorem higherResolutionExchangeEquation_of_actualTransport
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
    (hb : b = s ≫ Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
      (Functor.whiskerRight β (DerivedCategory.Plus.homologyFunctor C (q : ℤ))) ≫ t)
    (hres : ResolutionExchangeEquation R₁ R₂ G H α β I J φ)
    (htransport : WhiskeredTransportEquation s β t M
      (G.map (r₁.hom.app M))
      ((G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
        (R₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M)))
      ((DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
        (R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)))
      (r₂.inv.app (H.obj M))) :
    HigherResolutionExchangeEquation R₁ R₂ G H α I J φ q (b.app M) := by
  subst r₁
  subst r₂
  subst b
  exact higherResolutionExchangeEquation_of_transport R₁ R₂ G H α β I J φ q _ hres
    htransport

end CategoryTheory.Functor
