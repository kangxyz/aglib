/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetCoherence
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-! # Canonical target coherence for maps normalized by original derived units -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor
universe u v u' v' dA dB₀ dB₁
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B] [EnoughInjectives A]
  (hA : HasDerivedCategory.{dA} A)
  (hB₀ : HasDerivedCategory.{dB₀} B) (hB₁ : HasDerivedCategory.{dB₁} B)
  (F G : A ⥤ B) [F.Additive] [G.Additive] (τ : F ⟶ G)

/-- An original map retains the original quotient and the original derived units. -/
def DerivedModelNatTransUnitEquation
    (β : (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _) ⟶
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ G _ _))
    (K : CochainComplex.Plus A) : Prop :=
  (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ F _ _).app K ≫
      β.app ((@DerivedCategory.Plus.Q _ _ _ hA).obj K) =
    (@DerivedCategory.Plus.Q _ _ _ hB₀).map (τ.mapCochainComplexPlus.app K) ≫
      (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ G _ _).app K

/-- The whole target-model square for the original two maps. -/
def DerivedModelNatTransTargetEquation
    (β₀ : (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _) ⟶
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ G _ _))
    (β₁ : (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₁ F _ _) ⟶
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₁ G _ _)) : Prop :=
  whiskerRight β₀ (canonicalEquivalence hB₀ hB₁).functor ≫
      (rightDerivedFunctorPlusChangeTarget hA hB₀ hB₁ G).hom =
    (rightDerivedFunctorPlusChangeTarget hA hB₀ hB₁ F).hom ≫ β₁

/-- Original-unit normalized maps commute with native target comparison, without an
invertibility assumption on either the ordinary map or the derived map. -/
theorem rightDerivedFunctorPlusChangeTarget_natTrans
    (β₀ : (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _) ⟶
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ G _ _))
    (β₁ : (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₁ F _ _) ⟶
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₁ G _ _))
    (h₀ : ∀ K, DerivedModelNatTransUnitEquation hA hB₀ F G τ β₀ K)
    (h₁ : ∀ K, DerivedModelNatTransUnitEquation hA hB₁ F G τ β₁ K) :
    DerivedModelNatTransTargetEquation hA hB₀ hB₁ F G β₀ β₁ := by
  change _ = _
  apply rightDerivedTarget_ext (@DerivedCategory.Plus.Q _ _ _ hA) (CochainComplex.Plus.quasiIso A)
    (canonicalEquivalence hB₀ hB₁) (@rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _ _)
    (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₀ F _ _)
  intro K
  have h₀K := h₀ K
  have h₁K := h₁ K
  change _ = _ at h₀K h₁K
  dsimp only [NatTrans.comp_app, whiskerRight_app]
  rw [← Category.assoc, ← Functor.map_comp, h₀K, Functor.map_comp,
    Category.assoc, rightDerivedFunctorPlusChangeTarget_unit]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusChangeTarget_unit, Category.assoc, h₁K]
  simpa only [Functor.comp_map, Category.assoc] using congrArg
    (fun z => z ≫ (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hA hB₁ G _ _).app K)
    ((quotientCompCanonicalEquivalenceIso hB₀ hB₁).hom.naturality (τ.mapCochainComplexPlus.app K))

end CategoryTheory.Functor
