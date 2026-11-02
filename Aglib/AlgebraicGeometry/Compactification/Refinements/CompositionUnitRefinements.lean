/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # Original identity-pullback refinements of composition unit towers -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : DenseCompactification f)

/-- The right unit tower's first model maps to the supplied original ambient. -/
def rightUnitFirstRefinement : (rightUnit C).first ⟶ C where
  hom := (rightUnit C).middleOpen
  isProper_hom := by
    change IsProper (pullback.snd (𝟙 Y) C.p)
    infer_instance
  open_fac := (rightUnit C).first_j_middleOpen
  base_fac := by
    change pullback.snd (𝟙 Y) C.p ≫ C.p = pullback.fst (𝟙 Y) C.p
    exact pullback.condition.symm.trans (Category.comp_id _)

variable [QuasiCompact f]

/-- The left unit tower's first model maps to the literal identity compactification. -/
def leftUnitFirstRefinement :
    (leftUnit C).first ⟶ DenseCompactification.ofProper (𝟙 X) where
  hom := (leftUnit C).first.p
  isProper_hom := (leftUnit C).first.toCompactification.isProper_p
  open_fac := (leftUnit C).first.fac
  base_fac := Category.comp_id _

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition
