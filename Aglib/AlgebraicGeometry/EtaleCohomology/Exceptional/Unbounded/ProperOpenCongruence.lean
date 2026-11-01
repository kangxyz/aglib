/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel

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
theorem moduleUnboundedProperOpenMate_congr
    {g₁ g₂ : V ⟶ U} {f₁ f₂ : X ⟶ Y} (eg : g₁ = g₂) (ef : f₁ = f₂)
    (h₁ : IsPullback g₁ j' j f₁) (h₂ : IsPullback g₂ j' j f₂) :
    moduleUnboundedProperOpenMate g₁ j' j f₁ h₁ Λ ≫
        Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek j' Λ)
          (eqToHom (congrArg (fun f : X ⟶ Y => moduleUnboundedDerivedDirectImage Λ f) ef)) =
      Functor.whiskerRight
        (eqToHom (congrArg (fun g : V ⟶ U => moduleUnboundedDerivedDirectImage Λ g) eg))
          (moduleUnboundedDerivedLowerShriek j Λ) ≫
        moduleUnboundedProperOpenMate g₂ j' j f₂ h₂ Λ := by
  subst g₂
  subst f₂
  simp

omit [Etale j] [Etale j'] in
/-- Equality transport in the open sides keeps the actual lower-shriek equality
maps and the unchanged proper sides. -/
theorem moduleUnboundedProperOpenMate_congr_opens
    {j₁ j₂ : U ⟶ Y} {i₁ i₂ : V ⟶ X}
    [Etale j₁] [Etale j₂] [Etale i₁] [Etale i₂]
    (ej : j₁ = j₂) (ei : i₁ = i₂) (g : V ⟶ U) (f : X ⟶ Y)
    (h₁ : IsPullback g i₁ j₁ f) (h₂ : IsPullback g i₂ j₂ f) :
    moduleUnboundedProperOpenMate g i₁ j₁ f h₁ Λ ≫
        Functor.whiskerRight (eqToHom (moduleUnboundedDerivedLowerShriek_congr Λ ei))
          (moduleUnboundedDerivedDirectImage Λ f) =
      Functor.whiskerLeft (moduleUnboundedDerivedDirectImage Λ g)
          (eqToHom (moduleUnboundedDerivedLowerShriek_congr Λ ej)) ≫
        moduleUnboundedProperOpenMate g i₂ j₂ f h₂ Λ := by
  subst j₂
  subst i₂
  simp

end AlgebraicGeometry.Scheme.EtaleCohomology
