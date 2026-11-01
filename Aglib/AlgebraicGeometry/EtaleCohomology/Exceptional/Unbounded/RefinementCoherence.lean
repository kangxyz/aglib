/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementPullbackCoherence
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
theorem moduleUnboundedDerivedRefinementComparison_id :
    moduleUnboundedDerivedRefinementComparison (𝟙 C) Λ ≫
      Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek C.j Λ)
        (moduleUnboundedDerivedDirectImageIdIso Λ C.Xbar).hom ≫
      (Functor.rightUnitor (moduleUnboundedDerivedLowerShriek C.j Λ)).hom =
    𝟙 (moduleUnboundedDerivedLowerShriek C.j Λ) := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, moduleUnboundedDerivedRefinementComparison_app]
  erw [Category.comp_id]
  exact adjunctionUnitComparison_id (moduleUnboundedDerivedAdjunction Λ (𝟙 C.Xbar))
    (moduleUnboundedDerivedRefinementPullbackIso (𝟙 C) Λ)
    (moduleUnboundedDerivedInverseImageIdIso Λ C.Xbar)
    (moduleUnboundedDerivedDirectImageIdIso Λ C.Xbar)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ C.Xbar)
    (moduleUnboundedDerivedRefinementPullbackIso_id Λ C) K

end Identity

section Composition

variable {C D E : Hom.DenseCompactification f} (a : C ⟶ D) (b : D ⟶ E)
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{w₃} (ModuleSheaf E.Xbar Λ)]

/-- The original derived refinement transformation respects actual refinement composition. -/
theorem moduleUnboundedDerivedRefinementComparison_comp :
    moduleUnboundedDerivedRefinementComparison (a ≫ b) Λ ≫
      Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek C.j Λ)
        (moduleUnboundedDerivedDirectImageCompIso Λ b.hom a.hom).hom =
    moduleUnboundedDerivedRefinementComparison b Λ ≫
      Functor.whiskerRight (moduleUnboundedDerivedRefinementComparison a Λ)
        (moduleUnboundedDerivedDirectImage Λ b.hom) ≫
      (Functor.associator (moduleUnboundedDerivedLowerShriek C.j Λ)
        (moduleUnboundedDerivedDirectImage Λ a.hom)
        (moduleUnboundedDerivedDirectImage Λ b.hom)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, moduleUnboundedDerivedRefinementComparison_app]
  exact adjunctionUnitComparison_comp
    (moduleUnboundedDerivedAdjunction Λ b.hom) (moduleUnboundedDerivedAdjunction Λ a.hom)
    (moduleUnboundedDerivedAdjunction Λ (a.hom ≫ b.hom))
    (moduleUnboundedDerivedRefinementPullbackIso b Λ)
    (moduleUnboundedDerivedRefinementPullbackIso a Λ)
    (moduleUnboundedDerivedRefinementPullbackIso (a ≫ b) Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ b.hom a.hom)
    (moduleUnboundedDerivedDirectImageCompIso Λ b.hom a.hom)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ b.hom a.hom)
    (moduleUnboundedDerivedRefinementPullbackIso_comp Λ a b) K

end Composition

end AlgebraicGeometry.Scheme.EtaleCohomology
