/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Derived

/-! Derived maps vanishing on the complementary open factor through closed restriction. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wZ wX

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

include hcomp

/-- The original localization triangle factors any map whose open restriction is zero
through the original closed adjunction unit. -/
theorem moduleDerived_exists_comp_closedUnit_of_open_zero
    {M N : DerivedCategory.Plus (ModuleSheaf X Λ)} (a : M ⟶ N)
    (ha : (moduleDerivedInverseImage Λ j).map a = 0) :
    ∃ b : (moduleDerivedDirectImage Λ i).obj ((moduleDerivedInverseImage Λ i).obj M) ⟶ N,
      a = (moduleDerivedAdjunction Λ i).unit.app M ≫ b := by
  let T := moduleDerivedLocalizationTriangle j Λ i hcomp M
  let adj := moduleDerivedLowerShriekAdjunction j Λ
  have hT := moduleDerivedLocalizationTriangle_distinguished j Λ i hcomp M
  have h : adj.counit.app M ≫ a = 0 := by
    have he : (adj.homEquiv ((moduleDerivedInverseImage Λ j).obj M) N).symm
        ((moduleDerivedInverseImage Λ j).map a) = adj.counit.app M ≫ a := by
      rw [adj.homEquiv_counit]
      exact adj.counit.naturality a
    rw [← he, ha, adj.homAddEquiv_symm_zero]
  exact T.yoneda_exact₂ hT a h

/-- Maps with the same closed restriction act identically before a map
whose restriction to the complementary open is zero. -/
theorem moduleDerived_comp_eq_of_closed_eq_of_open_zero
    {L M N : DerivedCategory.Plus (ModuleSheaf X Λ)} (a b : L ⟶ M) (c : M ⟶ N)
    (hab : (moduleDerivedInverseImage Λ i).map a = (moduleDerivedInverseImage Λ i).map b)
    (hc : (moduleDerivedInverseImage Λ j).map c = 0) :
    a ≫ c = b ≫ c := by
  obtain ⟨d, hd⟩ := moduleDerived_exists_comp_closedUnit_of_open_zero j Λ i hcomp c hc
  let adj := moduleDerivedAdjunction Λ i
  have ha := adj.unit.naturality a
  have hb := adj.unit.naturality b
  change a ≫ adj.unit.app M =
    adj.unit.app L ≫ (moduleDerivedDirectImage Λ i).map
      ((moduleDerivedInverseImage Λ i).map a) at ha
  change b ≫ adj.unit.app M =
    adj.unit.app L ≫ (moduleDerivedDirectImage Λ i).map
      ((moduleDerivedInverseImage Λ i).map b) at hb
  rw [hd, ← Category.assoc, ← Category.assoc, ha, hb, hab]

end AlgebraicGeometry.Scheme.EtaleCohomology
