/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageRefinement
public import Aglib.CategoryTheory.NatTrans.ImageComparisonTargetEquation
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramTargetEquation

/-! # Descent of the original exceptional-to-ordinary comparison -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wD wM

section Triangles
variable (Λ : Type (u + 1)) [Ring Λ] {X C D S : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Two original structural triangles paste by native derived associativity. -/
theorem moduleUnboundedDerivedDirectImageOverIso_triangle (f : X ⟶ S)
    (jC : X ⟶ C) (jD : X ⟶ D) (a : C ⟶ D) (pC : C ⟶ S) (pD : D ⟶ S)
    (hj : jC ≫ a = jD) (hp : a ≫ pD = pC)
    (hC : jC ≫ pC = f) (hD : jD ≫ pD = f) :
    Functor.isoWhiskerLeft (moduleUnboundedDerivedDirectImage Λ jC)
        (moduleUnboundedDerivedDirectImageOverIso Λ pC pD a hp) ≪≫
      moduleUnboundedDerivedDirectImageOverIso Λ f pC jC hC =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageOverIso Λ jD a jC hj)
        (moduleUnboundedDerivedDirectImage Λ pD) ≪≫
      moduleUnboundedDerivedDirectImageOverIso Λ f pD jD hD := by
  subst jD
  simpa only [moduleUnboundedDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl] using
    moduleUnboundedDerivedDirectImageOverIso_comp Λ f pC pD jC a hC hp hD
end Triangles

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Every original refinement commutes with the original map to ordinary direct image. -/
theorem moduleUnboundedCompactificationToDirectImage_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    TargetComparisonEquation (moduleUnboundedCompactificationTransition Λ a)
      (moduleUnboundedCompactificationToDirectImage f Λ C)
      (moduleUnboundedCompactificationToDirectImage f Λ D) :=
  imageComparison_toTarget_equation
    (moduleUnboundedDerivedRefinementComparison a Λ)
    (moduleUnboundedLowerShriekToDirectImage Λ C.j)
    (moduleUnboundedLowerShriekToDirectImage Λ D.j)
    (moduleUnboundedDerivedDirectImageOverIso Λ D.j a.hom C.j a.open_fac)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a)
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac)
    (moduleUnboundedDerivedDirectImageOverIso Λ f D.p D.j D.fac)
    (moduleUnboundedDerivedProperRefinementComparison_toDirectImage_naturality
      Λ C.j D.j a.hom (Hom.DenseCompactification.isPullback_open a))
    (moduleUnboundedDerivedDirectImageOverIso_triangle Λ f C.j D.j a.hom C.p D.p
      a.open_fac a.base_fac C.fac D.fac)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Canonical comparison with every model preserves the same original map. -/
theorem moduleUnboundedCompactificationToDirectImage_comparison
    (C D : Hom.DenseCompactification f) :
    TargetComparisonEquation (moduleUnboundedCompactificationComparison f Λ N hN hΛ C D).hom
      (moduleUnboundedCompactificationToDirectImage f Λ D)
      (moduleUnboundedCompactificationToDirectImage f Λ C) := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison_targetEquation
    (moduleUnboundedCompactificationToDirectImage f Λ)
    (fun a => moduleUnboundedCompactificationToDirectImage_refinement f Λ a) C D

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The chosen map is computed through every original compactification. -/
theorem moduleExceptionalToDirectImageUnbounded_model (C : Hom.DenseCompactification f) :
    TargetComparisonEquation (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C).hom
      (moduleUnboundedCompactificationToDirectImage f Λ C)
      (moduleExceptionalToDirectImageUnbounded f Λ) :=
  moduleUnboundedCompactificationToDirectImage_comparison f Λ N hN hΛ
    (moduleExceptionalCompactification f) C

end AlgebraicGeometry.Scheme.EtaleCohomology
