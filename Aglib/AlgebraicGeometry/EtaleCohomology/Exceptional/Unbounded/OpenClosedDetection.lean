/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Unbounded
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenFullyFaithful

/-!
# Open and closed detection on the original unbounded derived category

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

/-- The original open and closed inverse images jointly detect unbounded isomorphisms. -/
theorem moduleUnboundedDerived_isIso_of_open_closed
    {K L : DerivedCategory (ModuleSheaf X Λ)} (a : K ⟶ L)
    [IsIso ((moduleUnboundedDerivedInverseImage Λ j).map a)]
    [IsIso ((moduleUnboundedDerivedInverseImage Λ i).map a)] : IsIso a := by
  let T := moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp
  have h₁ : IsIso ((T.map a).hom₁) := by
    apply (NatIso.isIso_map_iff (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleUnboundedDerivedLowerShriek j Λ).map
      ((moduleUnboundedDerivedInverseImage Λ j).map a))
    infer_instance
  have h₃ : IsIso ((T.map a).hom₃) := by
    apply (NatIso.isIso_map_iff (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleUnboundedDerivedDirectImage Λ i).map
      ((moduleUnboundedDerivedInverseImage Λ i).map a))
    infer_instance
  have h₂ : IsIso ((T.map a).hom₂) :=
    isIso₂_of_isIso₁₃ (T.map a)
      (moduleUnboundedLocalizationTriangleFunctor_distinguished j Λ i hcomp K)
      (moduleUnboundedLocalizationTriangleFunctor_distinguished j Λ i hcomp L) h₁ h₃
  exact (NatIso.isIso_map_iff (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp) a).mp h₂

/-- Isomorphisms are exactly those detected on the two complementary pieces. -/
theorem moduleUnboundedDerived_isIso_iff_open_closed
    {K L : DerivedCategory (ModuleSheaf X Λ)} (a : K ⟶ L) :
    IsIso a ↔ IsIso ((moduleUnboundedDerivedInverseImage Λ j).map a) ∧
      IsIso ((moduleUnboundedDerivedInverseImage Λ i).map a) := by
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hj, hi⟩
    exact moduleUnboundedDerived_isIso_of_open_closed j Λ i hcomp a

/-- Derived extension by zero restricts to zero on the complementary closed subscheme. -/
theorem isZero_moduleUnboundedDerivedInverseImage_lowerShriek
    (M : DerivedCategory (ModuleSheaf U Λ)) :
    IsZero ((moduleUnboundedDerivedInverseImage Λ i).obj
      ((moduleUnboundedDerivedLowerShriek j Λ).obj M)) := by
  let K := (moduleUnboundedDerivedLowerShriek j Λ).obj M
  let adj := moduleUnboundedDerivedAdjunction Λ i
  have hε : IsIso ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app K) :=
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).isIso_counit_app_of_iso (Iso.refl _)
  have hz : IsZero ((moduleUnboundedDerivedDirectImage Λ i).obj
      ((moduleUnboundedDerivedInverseImage Λ i).obj K)) :=
    (moduleUnboundedDerivedLocalizationTriangle j Λ i hcomp K).isZero₃_of_isIso₁
      (moduleUnboundedDerivedLocalizationTriangle_distinguished j Λ i hcomp K) hε
  have hη : adj.unit.app K = 0 := hz.eq_zero_of_tgt _
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← adj.left_triangle_components K, hη, Functor.map_zero, zero_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology
