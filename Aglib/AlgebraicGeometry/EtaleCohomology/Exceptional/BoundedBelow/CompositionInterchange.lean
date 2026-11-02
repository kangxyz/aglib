/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionHorizontalPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.VerticalPasting

/-! # Associativity of actual proper/open interchange in three Cartesian squares

Both larger squares are actual pastes. The result is the original map equation,
not an assumed coherent-composition field. Outer open/proper compositors and
canonical compactification transports are separate subsequent inputs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wA₀ wA₁ wA₂ wB₀ wB₁ wY wZ wC

variable (Λ : Type (u + 1)) [Ring Λ]
  {A₀ A₁ A₂ B₀ B₁ Y Z C : Scheme.{u}}
  (q₀ : A₀ ⟶ Y) (i₁ : Y ⟶ B₀) (m₀₁ : A₀ ⟶ A₁) (r₀₁ : A₁ ⟶ B₀)
  (q₁ : B₀ ⟶ Z) (i₂ : Z ⟶ C) (m₁₂ : B₀ ⟶ B₁) (r₁₂ : B₁ ⟶ C)
  (n : A₁ ⟶ A₂) (r₀₂ : A₂ ⟶ B₁)
  [Etale i₁] [Etale i₂] [Etale m₀₁] [Etale m₁₂] [Etale n]
  (sa : IsPullback q₀ m₀₁ i₁ r₀₁)
  (sb : IsPullback q₁ m₁₂ i₂ r₁₂)
  (sc : IsPullback r₀₁ n m₁₂ r₀₂)
  [HasDerivedCategory.{wA₀} (ModuleSheaf A₀ Λ)]
  [HasDerivedCategory.{wA₁} (ModuleSheaf A₁ Λ)]
  [HasDerivedCategory.{wA₂} (ModuleSheaf A₂ Λ)]
  [HasDerivedCategory.{wB₀} (ModuleSheaf B₀ Λ)]
  [HasDerivedCategory.{wB₁} (ModuleSheaf B₁ Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]

/-- The original three-square exchanges have the exact normalized associativity equation. -/
theorem moduleProperOpenInterchangeAssociativity :
    ImageInterchangeAssociativityEquation
      (moduleProperOpenMate Λ i₁ m₀₁ q₀ r₀₁ sa)
      (moduleProperOpenMate Λ i₂ m₁₂ q₁ r₁₂ sb)
      (moduleProperOpenMate Λ i₂ n (r₀₁ ≫ q₁) (r₀₂ ≫ r₁₂) (sc.paste_horiz sb))
      (moduleProperOpenMate Λ (i₁ ≫ m₁₂) (m₀₁ ≫ n) q₀ r₀₂ (sa.paste_vert sc))
      (moduleDerivedDirectImageCompIso Λ q₁ r₀₁)
      (moduleDerivedDirectImageCompIso Λ r₁₂ r₀₂)
      (moduleDerivedLowerShriekCompIso Λ m₁₂ i₁)
      (moduleDerivedLowerShriekCompIso Λ n m₀₁) :=
  imageInterchangeAssociativityEquation
    (moduleProperOpenMate Λ i₁ m₀₁ q₀ r₀₁ sa)
    (moduleProperOpenMate Λ i₂ m₁₂ q₁ r₁₂ sb)
    (moduleProperOpenMate Λ m₁₂ n r₀₁ r₀₂ sc)
    (moduleProperOpenMate Λ i₂ n (r₀₁ ≫ q₁) (r₀₂ ≫ r₁₂) (sc.paste_horiz sb))
    (moduleProperOpenMate Λ (i₁ ≫ m₁₂) (m₀₁ ≫ n) q₀ r₀₂ (sa.paste_vert sc))
    (moduleDerivedDirectImageCompIso Λ q₁ r₀₁)
    (moduleDerivedDirectImageCompIso Λ r₁₂ r₀₂)
    (moduleDerivedLowerShriekCompIso Λ m₁₂ i₁)
    (moduleDerivedLowerShriekCompIso Λ n m₀₁)
    (moduleProperOpenMate_vComp_actual Λ i₂ m₁₂ n q₁ r₀₁ r₁₂ r₀₂
      sb sc (sc.paste_horiz sb))
    (moduleProperOpenMate_hComp_interchange Λ m₁₂ i₁ n m₀₁ r₀₂ r₀₁ q₀
      sc sa (sa.paste_vert sc))

end AlgebraicGeometry.Scheme.EtaleCohomology
