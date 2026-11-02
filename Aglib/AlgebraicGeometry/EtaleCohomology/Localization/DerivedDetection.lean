/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Derived

/-!
# Open and closed detection on the original bounded-below derived category

The actual inverse images to a complementary open and closed subscheme jointly
detect isomorphisms. The proof uses the existing functorial localization triangle
and its natural vertex comparisons, without choosing new representatives or
changing any of the original derived maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

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

/-- The original open and closed inverse images jointly detect isomorphisms in D+. -/
theorem moduleDerived_isIso_of_open_closed
    {K L : DerivedCategory.Plus (ModuleSheaf X Λ)} (a : K ⟶ L)
    [IsIso ((moduleDerivedInverseImage Λ j).map a)]
    [IsIso ((moduleDerivedInverseImage Λ i).map a)] : IsIso a := by
  let T := moduleLocalizationTriangleFunctor j Λ i hcomp
  have h₁ : IsIso ((T.map a).hom₁) := by
    apply (NatIso.isIso_map_iff (moduleLocalizationFirstNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleDerivedLowerShriek j Λ).map
      ((moduleDerivedInverseImage Λ j).map a))
    infer_instance
  have h₃ : IsIso ((T.map a).hom₃) := by
    apply (NatIso.isIso_map_iff (moduleLocalizationThirdNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleDerivedDirectImage Λ i).map
      ((moduleDerivedInverseImage Λ i).map a))
    infer_instance
  have h₂ : IsIso ((T.map a).hom₂) :=
    isIso₂_of_isIso₁₃ (T.map a)
      (moduleLocalizationTriangleFunctor_distinguished j Λ i hcomp K)
      (moduleLocalizationTriangleFunctor_distinguished j Λ i hcomp L) h₁ h₃
  exact (NatIso.isIso_map_iff (moduleLocalizationMiddleNatIso j Λ i hcomp) a).mp h₂

/-- Isomorphisms in the original D+ are exactly those detected on the two complementary pieces. -/
theorem moduleDerived_isIso_iff_open_closed
    {K L : DerivedCategory.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    IsIso a ↔ IsIso ((moduleDerivedInverseImage Λ j).map a) ∧
      IsIso ((moduleDerivedInverseImage Λ i).map a) := by
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hj, hi⟩
    exact moduleDerived_isIso_of_open_closed j Λ i hcomp a

end AlgebraicGeometry.Scheme.EtaleCohomology
