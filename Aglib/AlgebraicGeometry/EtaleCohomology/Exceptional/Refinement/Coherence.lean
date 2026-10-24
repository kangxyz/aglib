/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.PullbackCoherence
public import Aglib.CategoryTheory.Adjunction.UnitComparisonCoherence

/-!
# Identity and composition for the original derived refinement transformation

The existing refinement transformation is the original derived adjunction unit
followed by direct image of the actual Cartesian open comparison. Its identity
and composition equations use precisely the original derived direct-image
comparisons. No replacement transformation, proper-base-change premise, or
invertibility assertion for the refinement transformation is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w w₁ w₂ w₃

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

section Identity

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]

/-- The original derived refinement transformation has the canonical identity value. -/
theorem moduleDerivedRefinementComparison_id :
    moduleDerivedRefinementComparison (𝟙 C) Λ ≫
      Functor.whiskerLeft (moduleDerivedLowerShriek C.j Λ)
        (moduleDerivedDirectImageIdIso Λ C.Xbar).hom ≫
      (Functor.rightUnitor (moduleDerivedLowerShriek C.j Λ)).hom =
    𝟙 (moduleDerivedLowerShriek C.j Λ) := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, moduleDerivedRefinementComparison_app]
  erw [Category.comp_id]
  exact adjunctionUnitComparison_id (moduleDerivedAdjunction Λ (𝟙 C.Xbar))
    (moduleDerivedRefinementPullbackIso (𝟙 C) Λ)
    (moduleDerivedInverseImageIdIso Λ C.Xbar) (moduleDerivedDirectImageIdIso Λ C.Xbar)
    (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ C.Xbar)
    (moduleDerivedRefinementPullbackIso_id Λ C) K

end Identity

section Composition

variable {C D E : Hom.DenseCompactification f} (a : C ⟶ D) (b : D ⟶ E)
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{w₃} (ModuleSheaf E.Xbar Λ)]

/-- The original derived refinement transformation respects actual refinement composition. -/
theorem moduleDerivedRefinementComparison_comp :
    moduleDerivedRefinementComparison (a ≫ b) Λ ≫
      Functor.whiskerLeft (moduleDerivedLowerShriek C.j Λ)
        (moduleDerivedDirectImageCompIso Λ b.hom a.hom).hom =
    moduleDerivedRefinementComparison b Λ ≫
      Functor.whiskerRight (moduleDerivedRefinementComparison a Λ)
        (moduleDerivedDirectImage Λ b.hom) ≫
      (Functor.associator (moduleDerivedLowerShriek C.j Λ)
        (moduleDerivedDirectImage Λ a.hom) (moduleDerivedDirectImage Λ b.hom)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, moduleDerivedRefinementComparison_app]
  exact adjunctionUnitComparison_comp
    (moduleDerivedAdjunction Λ b.hom) (moduleDerivedAdjunction Λ a.hom)
    (moduleDerivedAdjunction Λ (a.hom ≫ b.hom))
    (moduleDerivedRefinementPullbackIso b Λ) (moduleDerivedRefinementPullbackIso a Λ)
    (moduleDerivedRefinementPullbackIso (a ≫ b) Λ)
    (moduleDerivedInverseImageCompIso Λ b.hom a.hom)
    (moduleDerivedDirectImageCompIso Λ b.hom a.hom)
    (conjugateEquiv_moduleDerivedInverseImageCompIso_hom Λ b.hom a.hom)
    (moduleDerivedRefinementPullbackIso_comp Λ a b) K

end Composition

end AlgebraicGeometry.Scheme.EtaleCohomology
