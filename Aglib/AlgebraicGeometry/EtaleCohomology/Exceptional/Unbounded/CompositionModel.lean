/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenComparison
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Composition

/-! # Composition through a supplied actual compactification tower

The comparison is the original proper/open comparison, followed by the original
open and proper compositors. The three middle model families are independent;
the source ambient scheme uses exactly the composite compactification's model.
This is a supplied-tower natural isomorphism on all unbounded objects over the
stated torsion coefficient ring. Independence of the tower requires
the additional refinement cube, and is not claimed here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG

/-- Literal equality transport between two specified etale maps. -/
theorem moduleUnboundedDerivedLowerShriek_congr
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    {j k : X ⟶ Y} [Etale j] [Etale k] (h : j = k) :
    moduleUnboundedDerivedLowerShriek j Λ = moduleUnboundedDerivedLowerShriek k Λ := by
  subst k
  rfl

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  (C : Hom.CompactifiedComposition f g)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Original proper/open interchange followed by the original open and proper compositors. -/
def moduleUnboundedCompactifiedCompositionIso :
    moduleUnboundedCompactificationFunctor f Λ C.first ⋙
        moduleUnboundedCompactificationFunctor g Λ C.targetCompactification ≅
      moduleUnboundedCompactificationFunctor (f ≫ g) Λ C.composite := by
  let : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
    compositeModels C.composite
  let e := moduleUnboundedProperOpenComparisonIso Λ C.sourceCompactification.p C.first.p
    C.targetCompactification.j C.middleOpen C.isPullback_middleOpen N hN hΛ
  let c : moduleUnboundedDerivedLowerShriek C.first.j Λ ⋙
      moduleUnboundedDerivedLowerShriek C.middleOpen Λ ≅
      moduleUnboundedDerivedLowerShriek C.sourceCompactification.j Λ :=
    (moduleUnboundedDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
      eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ C.first_j_middleOpen)
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek C.first.j Λ) e)
      (moduleUnboundedDerivedDirectImage Λ C.targetCompactification.p) ≪≫
    Functor.isoWhiskerRight c
      (moduleUnboundedDerivedDirectImage Λ C.sourceCompactification.p ⋙
        moduleUnboundedDerivedDirectImage Λ C.targetCompactification.p) ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek C.sourceCompactification.j Λ)
      (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
