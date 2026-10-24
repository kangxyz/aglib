/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda

/-!
# Test maps into the regular tower colimit

Native regular-cardinal factorization places an actual test map at a stage.
A specified later nullhomotopy then extends along the original colimit cocone.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {J : Type w} [SmallCategory J]
  (F : J ⥤ CochainComplex C ℤ)
  [∀ (i j : J) (f : i ⟶ j), Mono (F.map f)]
  {c : Cocone F} (hc : IsColimit c)
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (A : CochainComplex C ℤ)

include hc in
/-- Every actual map from a bounded test into the native colimit is nullhomotopic
if each stage map is killed at some actual later stage. -/
lemma nonempty_homotopy_zero_of_colimit_stage
    (hsize : HasCardinalLT (Subobject A) κ)
    (hkill : ∀ j (f : A ⟶ F.obj j),
      ∃ (k : J) (g : j ⟶ k), Nonempty (Homotopy (f ≫ F.map g) 0))
    (z : A ⟶ c.pt) : Nonempty (Homotopy z 0) := by
  obtain ⟨j, f, hf⟩ := CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity hc hsize z
  obtain ⟨k, g, ⟨h⟩⟩ := hkill j f
  rw [hf]
  refine ⟨?_⟩
  simpa only [Category.assoc, c.w g, zero_comp] using h.compRight (c.ι.app k)

end CochainComplex
