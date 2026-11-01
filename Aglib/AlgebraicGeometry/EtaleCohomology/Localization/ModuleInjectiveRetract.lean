/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleRestrictionDetection
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Size
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Original injective module coefficients split over open and closed parts

The first coordinate is the original open inverse-image unit. The second is
the original closed adjunct of an injective presentation. Joint restriction
detection proves monicity, and injectivity splits that unchanged arrow.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

private theorem map_eq_of_unit_comp_eq
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {T M : C} (b c : T ⟶ M)
    (h : b ≫ adj.unit.app M = c ≫ adj.unit.app M) : L.map b = L.map c := by
  have he := congrArg (fun k => L.map k ≫ adj.counit.app (L.obj M)) h
  simpa only [Functor.map_comp, Category.assoc,
    adj.left_triangle_components, Category.comp_id] using he

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)
  (Λ : Type (u + 1)) [Ring Λ]

include hcomp

/-- The original open unit and a monic closed adjunct are jointly monic. -/
theorem module_open_closed_adjunct_mono
    (M : ModuleSheaf X Λ) (J : ModuleSheaf Z Λ)
    (a : (moduleInverseImage i Λ).obj M ⟶ J) [Mono a] :
    Mono (biprod.lift ((moduleInverseImageAdjunction j Λ).unit.app M)
      ((moduleInverseImageAdjunction i Λ).homEquiv M J a)) := by
  constructor
  intro T b c h
  have hopen : b ≫ (moduleInverseImageAdjunction j Λ).unit.app M =
      c ≫ (moduleInverseImageAdjunction j Λ).unit.app M := by
    have he := congrArg (fun k => k ≫ biprod.fst) h
    simpa only [Category.assoc, biprod.lift_fst] using he
  have hclosed : b ≫ (moduleInverseImageAdjunction i Λ).homEquiv M J a =
      c ≫ (moduleInverseImageAdjunction i Λ).homEquiv M J a := by
    have he := congrArg (fun k => k ≫ biprod.snd) h
    simpa only [Category.assoc, biprod.lift_snd] using he
  apply module_map_eq_of_open_closed_restrictions j i hcomp Λ b c
  · exact map_eq_of_unit_comp_eq (moduleInverseImageAdjunction j Λ) b c hopen
  · apply (cancel_mono a).mp
    apply ((moduleInverseImageAdjunction i Λ).homEquiv T J).injective
    exact ((moduleInverseImageAdjunction i Λ).homEquiv_naturality_left b a).trans
      (hclosed.trans
        ((moduleInverseImageAdjunction i Λ).homEquiv_naturality_left c a).symm)

/-- Every genuine injective coefficient is a retract of the original open
restriction's direct image and an injective closed coefficient's direct image.
No injectivity of a forgotten coefficient or geometric pullback is asserted. -/
theorem exists_moduleInjective_open_closed_retract
    (I : ModuleSheaf X Λ) [Injective I] :
    ∃ J : ModuleSheaf Z Λ, Injective J ∧
      ∃ a : (moduleInverseImage i Λ).obj I ⟶ J, Mono a ∧
        ∃ r : ((moduleDirectImage j Λ).obj ((moduleInverseImage j Λ).obj I)) ⊞
            ((moduleDirectImage i Λ).obj J) ⟶ I,
          biprod.lift ((moduleInverseImageAdjunction j Λ).unit.app I)
            ((moduleInverseImageAdjunction i Λ).homEquiv I J a) ≫ r = 𝟙 I := by
  let : EnoughInjectives (ModuleSheaf Z Λ) :=
    SheafOfModules.enoughInjectivesLarge.{u + 1, u, 0} (constantRing Z Λ)
  obtain ⟨P⟩ := EnoughInjectives.presentation ((moduleInverseImage i Λ).obj I)
  let q := biprod.lift ((moduleInverseImageAdjunction j Λ).unit.app I)
    ((moduleInverseImageAdjunction i Λ).homEquiv I P.J P.f)
  let : Mono q := module_open_closed_adjunct_mono j i hcomp Λ I P.J P.f
  exact ⟨P.J, inferInstance, P.f, inferInstance, Injective.factorThru (𝟙 I) q,
    Injective.comp_factorThru (𝟙 I) q⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
