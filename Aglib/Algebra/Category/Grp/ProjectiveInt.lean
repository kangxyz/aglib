/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-! # Projectivity of the original lifted integer group -/

@[expose] public noncomputable section

open CategoryTheory

namespace AddCommGrpCat

universe v

/-- Lift the original integer generator through an epi, then extend it by its
integer multiples. The source is exactly the native lifted integer group. -/
theorem projective_uliftZ : Projective (AddCommGrpCat.of (ULift.{v} ℤ)) := by
  constructor
  intro E X f e he
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective e).mp he (f (ULift.up 1))
  let g := (AddCommGrpCat.uliftZMultiplesAddEquiv E).symm x
  refine ⟨g, ?_⟩
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv X).injective
  have hg : g (ULift.up 1) = x :=
    (AddCommGrpCat.uliftZMultiplesAddEquiv E).apply_symm_apply x
  change e (g (ULift.up 1)) = f (ULift.up 1)
  rw [hg]
  exact hx

end AddCommGrpCat
