/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Diagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Independence

/-! # Original refinement transitions with independent middle models

The geometric identity is allowed to carry different native derived models on
its two sides. Composition retains the original refinement-unit maps and proper
image compositors. No same-scheme instance is identified implicitly.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wD wE
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- A single original value, without imposing a family of middle models. -/
abbrev moduleCompactificationValue (C : Hom.DenseCompactification f)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)] :=
  (moduleTorsionCohomologyPlus X Λ).ι ⋙
    moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p

section Mixed
variable {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  [hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The original refinement transition with independently specified models. -/
def moduleCompactificationMixedTransition :
    moduleCompactificationValue Λ D ⟶ moduleCompactificationValue Λ C :=
  Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
    (CategoryTheory.imageComparison (moduleDerivedRefinementComparison a Λ)
      (moduleDerivedRefinementDirectImageIso Λ a))

/-- The original mixed-model map is invertible on the same torsion source. -/
instance moduleCompactificationMixedTransition_isIso :
    IsIso (moduleCompactificationMixedTransition Λ a) := by
  have (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
      IsIso ((moduleCompactificationMixedTransition Λ a).app K) := by
    let : IsIso ((moduleDerivedRefinementComparison a Λ).app K.obj) :=
      moduleDerivedRefinementComparison_isIso a Λ K.obj K.property
    exact CategoryTheory.imageComparison_isIso_app (moduleDerivedRefinementComparison a Λ)
      (moduleDerivedRefinementDirectImageIso Λ a) K.obj
  exact NatIso.isIso_of_isIso_app _

variable {E : Hom.DenseCompactification f} (b : D ⟶ E)
  [hE : HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)]

/-- Composition remains valid when all three middle models are independent. -/
theorem moduleCompactificationMixedTransition_comp :
    moduleCompactificationMixedTransition Λ (a ≫ b) =
      moduleCompactificationMixedTransition Λ b ≫ moduleCompactificationMixedTransition Λ a := by
  have h := CategoryTheory.imageComparison_comp (moduleDerivedRefinementComparison a Λ)
    (moduleDerivedRefinementComparison b Λ) (moduleDerivedRefinementComparison (a ≫ b) Λ)
    (moduleDerivedDirectImageCompIso Λ b.hom a.hom)
    (moduleDerivedRefinementDirectImageIso Λ a) (moduleDerivedRefinementDirectImageIso Λ b)
    (moduleDerivedRefinementDirectImageIso Λ (a ≫ b))
    (moduleDerivedRefinementComparison_comp Λ a b)
    (moduleDerivedRefinementDirectImageIso_comp Λ a b)
  simpa only [moduleCompactificationMixedTransition, Functor.whiskerLeft_comp] using
    congrArg (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι) h
end Mixed

end AlgebraicGeometry.Scheme.EtaleCohomology
