/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageIdentity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinement
public import Aglib.CategoryTheory.Adjunction.IdentitySourceOuterComparison

/-! # The original proper-refinement map is the canonical outer-adjoint comparison

The comparison comes from the original identity-source square. Its equality
with Mathlib's canonical triple map uses the original mixed-mate square and
the original identity normalizations, without a chosen exceptional unit law.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wX
variable (Λ : Type (u + 1)) [Ring Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  (h : IsPullback (𝟙 U) (𝟙 U) j j)

omit [IsOpenImmersion j] in
/-- The original diagonal structural direct-image square is literally the identity. -/
theorem moduleDerivedDirectImageSquareIso_diagonal :
    moduleDerivedDirectImageSquareIso Λ j (𝟙 U) j (𝟙 U) h.flip.w =
      Iso.refl (moduleDerivedDirectImage Λ (𝟙 U) ⋙ moduleDerivedDirectImage Λ j) := by
  simp only [moduleDerivedDirectImageSquareIso, eqToIso_refl, Iso.refl_trans,
    Iso.symm_self_id]

/-- The actual original derived-unit refinement equals the canonical `j! → Rj*` map. -/
theorem moduleDerivedProperRefinementComparison_toDirectImage :
    moduleDerivedProperRefinementComparison (𝟙 U) j j h Λ ≫
      Functor.whiskerRight (moduleDerivedLowerShriekIdIso Λ U).hom
        (moduleDerivedDirectImage Λ j) ≫
      (Functor.leftUnitor (moduleDerivedDirectImage Λ j)).hom =
      moduleDerivedLowerShriekToDirectImage Λ j := by
  apply identitySourceOuterComparison
    (moduleProperOpenMate Λ j (𝟙 U) (𝟙 U) j h.flip)
    _ _ (moduleDerivedLowerShriekToDirectImage Λ (𝟙 U))
    (moduleDerivedDirectImageSquareIso Λ j (𝟙 U) j (𝟙 U) h.flip.w).hom
    (moduleDerivedDirectImageIdIso Λ U) (moduleDerivedLowerShriekIdIso Λ U)
  · intro K
    exact (moduleDerivedProperRefinementComparison_identitySourceMate
      (𝟙 U) j j h Λ K).symm
  · exact moduleDerivedLowerShriekToDirectImage_id Λ U
  · exact congrArg Iso.hom (moduleDerivedDirectImageSquareIso_diagonal Λ j h)
  · exact moduleProperOpenMate_toDirectImageSquare Λ j (𝟙 U) (𝟙 U) j h.flip

end AlgebraicGeometry.Scheme.EtaleCohomology
