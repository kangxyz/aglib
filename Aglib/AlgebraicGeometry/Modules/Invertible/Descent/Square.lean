/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Actual line-bundle lifts through a commuting square

Pulling back a specified lift retains its isomorphism with the pullback of
the original fibre bundle. The square need only commute.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- Surjectivity on the original Picard classes supplies an actual bundle
and an actual pullback isomorphism for each specified fibre bundle. -/
theorem exists_lineBundle_lift_of_pullbackClass_surjective
    {X Y : Scheme.{u}} (i : X ⟶ Y)
    (h : Function.Surjective (pullbackClass i)) (L : LineBundle X) :
    ∃ M : LineBundle Y, Nonempty ((pullback i).obj M.val ≅ L.val) := by
  obtain ⟨a, ha⟩ := h (classOf X L)
  induction a using Quotient.inductionOn with
  | h M => exact ⟨M, Quotient.exact ha⟩

/-- Pull a given line-bundle lifting property through the original commuting
square. No cartesianness or residue-field isomorphism is required. -/
theorem exists_lineBundle_pullback_of_square
    {X Z K L : Scheme.{u}} (a : X ⟶ Z) (i : K ⟶ X)
    (j : L ⟶ Z) (g : K ⟶ L) (h : i ≫ a = g ≫ j)
    (hlift : ∀ C : LineBundle L, ∃ V : LineBundle Z,
      Nonempty ((pullback j).obj V.val ≅ C.val)) (C : LineBundle L) :
    ∃ W : LineBundle X,
      Nonempty ((pullback i).obj W.val ≅ (pullback g).obj C.val) := by
  obtain ⟨V, ⟨e⟩⟩ := hlift C
  refine ⟨pullbackLineBundle a V, ⟨?_⟩⟩
  exact (pullbackComp i a).app V.val ≪≫ (pullbackCongr h).app V.val ≪≫
    ((pullbackComp g j).symm.app V.val) ≪≫ (pullback g).mapIso e

end AlgebraicGeometry.Scheme.Modules.Invertible
