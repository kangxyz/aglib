/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.OrdinaryExchange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherComparisons

/-! # The whole ordinary higher exchange from its actual unit

The selected-model source, mate and target form an actual natural transformation.
The original resolution comparison identifies each component with the ordinary
exchange formula. This constructs that entire ordinary transformation, including
naturality, without taking the wanted ordinary transformation as input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [EnoughInjectives D]
  [HasDerivedCategory.{wD} D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)
  (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
    H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)

omit [PreservesFiniteLimits H] [PreservesFiniteColimits H] in
/-- Transport the actual derived exchange through its canonical higher comparisons. -/
def actualHigherExchangeTransport (q : ℕ) :
    R₁.rightDerived q ⋙ G ⟶ H ⋙ R₂.rightDerived q :=
  (higherExchangeSourceIso R₁ G q).hom ≫
    whiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
      (whiskerRight β (DerivedCategory.Plus.homologyFunctor C (q : ℤ))) ≫
    (higherExchangeTargetIso H R₂ q).hom

variable (hunit : ∀ K, ActualDerivedUnitEquation R₁ R₂ G H α β K)

include hunit in
/-- The actual transport has the original ordinary resolution-homology component. -/
theorem actualHigherExchangeTransport_app (M : B) (q : ℕ) :
    (actualHigherExchangeTransport R₁ R₂ G H β q).app M =
      ordinaryHigherExchangeApp R₁ R₂ G H α M q :=
  higherExchangeTransport_app_eq_ordinary R₁ R₂ G H α β q
    (R₁.rightDerivedSingleHomologyIso q) (R₂.rightDerivedSingleHomologyIso q) rfl rfl
    (higherExchangeSourceIso R₁ G q).hom (higherExchangeTargetIso H R₂ q).hom
    (actualHigherExchangeTransport R₁ R₂ G H β q) rfl hunit
    (higherExchangeSourceIso_hom_app R₁ G q)
    (higherExchangeTargetIso_hom_app H R₂ q) M

include hunit in
/-- The complete ordinary exchange, with its literal ordinary component and proved naturality. -/
def ordinaryHigherExchangeOfActualUnit (q : ℕ) :
    R₁.rightDerived q ⋙ G ⟶ H ⋙ R₂.rightDerived q where
  app M := ordinaryHigherExchangeApp R₁ R₂ G H α M q
  naturality {M N} a := by
    rw [← actualHigherExchangeTransport_app R₁ R₂ G H α β hunit M q,
      ← actualHigherExchangeTransport_app R₁ R₂ G H α β hunit N q]
    exact (actualHigherExchangeTransport R₁ R₂ G H β q).naturality a

/-- The component is the original ordinary formula, independently of the comparison proof. -/
theorem ordinaryHigherExchangeOfActualUnit_app (M : B) (q : ℕ) :
    (ordinaryHigherExchangeOfActualUnit R₁ R₂ G H α β hunit q).app M =
      ordinaryHigherExchangeApp R₁ R₂ G H α M q := rfl

/-- The entire ordinary transformation equals the original actual selected-model transport. -/
theorem ordinaryHigherExchangeOfActualUnit_eq_transport (q : ℕ) :
    ordinaryHigherExchangeOfActualUnit R₁ R₂ G H α β hunit q =
      actualHigherExchangeTransport R₁ R₂ G H β q := by
  apply NatTrans.ext
  funext M
  exact (actualHigherExchangeTransport_app R₁ R₂ G H α β hunit M q).symm

end CategoryTheory.Functor
