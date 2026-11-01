/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition

/-! # Equality transport of the original proper/open mate

Changing equal proper sides with the opens fixed retains the literal original
mate. Both functor transports are the original equality morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wV wX wY

variable (Λ : Type (u + 1)) [Ring Λ]
  {U V X Y : Scheme.{u}} (j : U ⟶ Y) (j' : V ⟶ X)
  [Etale j] [Etale j']
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]

/-- Original mixed-mate transport along equal side maps, as a whole
natural-transformation equality with the specified equality morphisms. -/
theorem moduleProperOpenMate_congr
    {g₁ g₂ : V ⟶ U} {f₁ f₂ : X ⟶ Y} (eg : g₁ = g₂) (ef : f₁ = f₂)
    (h₁ : IsPullback g₁ j' j f₁) (h₂ : IsPullback g₂ j' j f₂) :
    moduleProperOpenMate Λ j j' g₁ f₁ h₁ ≫
        Functor.whiskerLeft (moduleDerivedLowerShriek j' Λ)
          (eqToHom (congrArg (fun f : X ⟶ Y => moduleDerivedDirectImage Λ f) ef)) =
      Functor.whiskerRight (eqToHom (congrArg (fun g : V ⟶ U => moduleDerivedDirectImage Λ g) eg))
          (moduleDerivedLowerShriek j Λ) ≫
        moduleProperOpenMate Λ j j' g₂ f₂ h₂ := by
  subst g₂
  subst f₂
  simp

omit [Etale j] [Etale j'] in
/-- Equality transport in the open sides keeps the actual lower-shriek equality
maps and the unchanged proper sides. -/
theorem moduleProperOpenMate_congr_opens
    {j₁ j₂ : U ⟶ Y} {i₁ i₂ : V ⟶ X}
    [Etale j₁] [Etale j₂] [Etale i₁] [Etale i₂]
    (ej : j₁ = j₂) (ei : i₁ = i₂) (g : V ⟶ U) (f : X ⟶ Y)
    (h₁ : IsPullback g i₁ j₁ f) (h₂ : IsPullback g i₂ j₂ f) :
    moduleProperOpenMate Λ j₁ i₁ g f h₁ ≫
        Functor.whiskerRight (eqToHom (moduleDerivedLowerShriek_congr Λ ei))
          (moduleDerivedDirectImage Λ f) =
      Functor.whiskerLeft (moduleDerivedDirectImage Λ g)
          (eqToHom (moduleDerivedLowerShriek_congr Λ ej)) ≫
        moduleProperOpenMate Λ j₂ i₂ g f h₂ := by
  subst j₂
  subst i₂
  simp

end AlgebraicGeometry.Scheme.EtaleCohomology
