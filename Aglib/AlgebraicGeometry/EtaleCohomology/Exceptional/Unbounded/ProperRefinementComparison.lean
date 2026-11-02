/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedOpen

/-! # The original unit comparison for a Cartesian open refinement

The exact Cartesian open comparison is localized on the native unbounded
categories. The refinement map is the original unbounded adjunction unit followed
by this comparison, with independently sized derived models at all vertices.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wC wD
variable {X Y₁ Y₂ : Scheme.{u}} (j₁ : X ⟶ Y₁) (j₂ : X ⟶ Y₂)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : Y₁ ⟶ Y₂)
  (sq : IsPullback j₁ (𝟙 X) h j₂)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf Y₁ Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf Y₂ Λ)]

/-- The original Cartesian open identity, localized without a boundedness restriction. -/
def moduleUnboundedDerivedProperRefinementPullbackIso :
    moduleUnboundedDerivedLowerShriek j₂ Λ ⋙ moduleUnboundedDerivedInverseImage Λ h ≅
      moduleUnboundedDerivedLowerShriek j₁ Λ :=
  Functor.mapDerivedCategoryCompIso (moduleLowerShriek j₂ Λ) (moduleInverseImage h Λ) ≪≫
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) _ _ _ _
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex
          (moduleLowerShriekCartesianIdentityIso j₁ j₂ h
            sq.flip Λ) (.up ℤ))
        DerivedCategory.Q)

/-- The same original unit defines the genuine unbounded refinement map. -/
def moduleUnboundedDerivedProperRefinementComparison :
    moduleUnboundedDerivedLowerShriek j₂ Λ ⟶
      moduleUnboundedDerivedLowerShriek j₁ Λ ⋙ moduleUnboundedDerivedDirectImage Λ h :=
  (Functor.rightUnitor (moduleUnboundedDerivedLowerShriek j₂ Λ)).inv ≫
    Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek j₂ Λ)
      (moduleUnboundedDerivedAdjunction Λ h).unit ≫
    (Functor.associator (moduleUnboundedDerivedLowerShriek j₂ Λ)
      (moduleUnboundedDerivedInverseImage Λ h)
      (moduleUnboundedDerivedDirectImage Λ h)).inv ≫
    Functor.whiskerRight (moduleUnboundedDerivedProperRefinementPullbackIso j₁ j₂ h sq Λ).hom
      (moduleUnboundedDerivedDirectImage Λ h)

/-- Every component retains the actual unbounded unit and the original open comparison. -/
theorem moduleUnboundedDerivedProperRefinementComparison_app
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedDerivedProperRefinementComparison j₁ j₂ h sq Λ).app K =
      (moduleUnboundedDerivedAdjunction Λ h).unit.app
          ((moduleUnboundedDerivedLowerShriek j₂ Λ).obj K) ≫
        (moduleUnboundedDerivedDirectImage Λ h).map
          ((moduleUnboundedDerivedProperRefinementPullbackIso j₁ j₂ h sq Λ).hom.app K) := by
  simp [moduleUnboundedDerivedProperRefinementComparison]

omit [IsOpenImmersion j₁] [IsOpenImmersion j₂]
  [HasDerivedCategory.{wC} (ModuleSheaf Y₁ Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf Y₂ Λ)] in
/-- The generalized comparison is literally the existing dense refinement comparison. -/
theorem moduleUnboundedDerivedProperRefinementComparison_dense
    {S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    {C D : Hom.DenseCompactification f} (a : C ⟶ D)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)] :
    moduleUnboundedDerivedProperRefinementComparison C.j D.j a.hom
      (Hom.DenseCompactification.isPullback_open a) Λ =
      moduleUnboundedDerivedRefinementComparison a Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
