/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitProperFace
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorizationCoherence

/-! # The actual central mixed mate contracts through the original identity factorization -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wY wA wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ))
  (hA : HasDerivedCategory.{wA} (ModuleSheaf (rightUnitFirstAmbient C) Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf Y Λ))

/-- The original central mate, proper compositor and refinement comparison contract to the
original identity-factorization isomorphism; no chosen exceptional unit equation is assumed. -/
theorem moduleRightUnitMiddleEquation :
    RightUnitMiddleEquation
      (moduleRightUnitCentralMate C Λ hY hA hB hD)
      (@moduleRightUnitMiddleOpenToDirect _ _ f C Λ _ hA hB)
      (moduleRightUnitProperFaceContraction C Λ hY hB hD)
      (moduleRightUnitMiddleOverIso C Λ hY hA hB)
      (moduleDerivedIdentityFactorizationIso Λ Y hY hD) :=
  rightUnitMiddleEquation_of_outerComparison
    (M := @moduleDerivedLowerShriek (rightUnitFirstAmbient C) C.Xbar
      (rightUnitMiddleOpen C) _ Λ _ hA hB)
    (N := @moduleDerivedDirectImage C.Xbar Λ _ (rightUnitFirstAmbient C)
      (rightUnitMiddleOpen C) hB hA)
    (Q := @moduleDerivedDirectImage Y Λ _ (rightUnitFirstAmbient C)
      (Hom.CompactifiedComposition.rightUnit C).first.p hY hA)
    (P := @moduleDerivedDirectImage Y Λ _ C.Xbar C.p hD hB)
    (P₀ := @moduleDerivedDirectImage Y Λ _ C.Xbar (C.p ≫ 𝟙 Y) hY hB)
    (I := @moduleDerivedLowerShriek Y Y (𝟙 Y) _ Λ _ hY hD)
    (S := @moduleDerivedDirectImage Y Λ _ Y (𝟙 Y) hD hY)
    (R := @moduleDerivedDirectImage Y Λ _ Y (𝟙 Y) hY hD)
    (moduleRightUnitCentralMate C Λ hY hA hB hD)
    (@moduleRightUnitMiddleOpenToDirect _ _ f C Λ _ hA hB)
    (@moduleDerivedLowerShriekToDirectImage Λ _ Y Y (𝟙 Y) _ hY hD)
    (moduleRightUnitStructuralSquare C Λ hY hA hB hD)
    (moduleRightUnitProperFaceContraction C Λ hY hB hD)
    (moduleRightUnitMiddleOverIso C Λ hY hA hB)
    (moduleRightUnitIdentityImageContraction Λ hY hD)
    (moduleDerivedIdentityFactorizationIso Λ Y hY hD)
    (moduleRightUnitMiddleOuterEquation C Λ hY hA hB hD)
    (moduleRightUnitProperFaceEquation C Λ hY hA hB hD)
    (moduleDerivedIdentityOuter_contraction Λ Y hY hD)

end AlgebraicGeometry.Scheme.EtaleCohomology
