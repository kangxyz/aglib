/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedOpen

/-! # The original unit comparison for an unbounded compactification refinement

The exact Cartesian open comparison is localized on the native unbounded
categories. The refinement map is the original unbounded adjunction unit followed
by this comparison, with independently sized derived models at all vertices.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The original Cartesian open identity, localized without a boundedness restriction. -/
def moduleUnboundedDerivedRefinementPullbackIso :
    moduleUnboundedDerivedLowerShriek D.j Λ ⋙ moduleUnboundedDerivedInverseImage Λ a.hom ≅
      moduleUnboundedDerivedLowerShriek C.j Λ :=
  Functor.mapDerivedCategoryCompIso (moduleLowerShriek D.j Λ) (moduleInverseImage a.hom Λ) ≪≫
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) _ _ _ _
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex
          (moduleLowerShriekCartesianIdentityIso C.j D.j a.hom
            (Hom.DenseCompactification.isPullback_open a).flip Λ) (.up ℤ))
        DerivedCategory.Q)

/-- The same original unit defines the genuine unbounded refinement map. -/
def moduleUnboundedDerivedRefinementComparison :
    moduleUnboundedDerivedLowerShriek D.j Λ ⟶
      moduleUnboundedDerivedLowerShriek C.j Λ ⋙ moduleUnboundedDerivedDirectImage Λ a.hom :=
  (Functor.rightUnitor (moduleUnboundedDerivedLowerShriek D.j Λ)).inv ≫
    Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek D.j Λ)
      (moduleUnboundedDerivedAdjunction Λ a.hom).unit ≫
    (Functor.associator (moduleUnboundedDerivedLowerShriek D.j Λ)
      (moduleUnboundedDerivedInverseImage Λ a.hom)
      (moduleUnboundedDerivedDirectImage Λ a.hom)).inv ≫
    Functor.whiskerRight (moduleUnboundedDerivedRefinementPullbackIso a Λ).hom
      (moduleUnboundedDerivedDirectImage Λ a.hom)

/-- Every component retains the actual unbounded unit and the original open comparison. -/
theorem moduleUnboundedDerivedRefinementComparison_app
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedDerivedRefinementComparison a Λ).app K =
      (moduleUnboundedDerivedAdjunction Λ a.hom).unit.app
          ((moduleUnboundedDerivedLowerShriek D.j Λ).obj K) ≫
        (moduleUnboundedDerivedDirectImage Λ a.hom).map
          ((moduleUnboundedDerivedRefinementPullbackIso a Λ).hom.app K) := by
  simp [moduleUnboundedDerivedRefinementComparison]

end AlgebraicGeometry.Scheme.EtaleCohomology
