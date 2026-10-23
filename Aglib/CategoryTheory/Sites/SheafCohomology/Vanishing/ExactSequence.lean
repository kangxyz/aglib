/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Vanishing from the original sheaf cohomology exact sequence

These abstract lemmas use the original connecting homomorphism. They do not
replace the geometric producers of the vanishing or surjectivity hypotheses.
-/

@[expose] public noncomputable section

universe c v a e

namespace CategoryTheory.Sheaf.H

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}] [HasExt.{e} (Sheaf J AddCommGrpCat.{a})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{a})}

/-- Surjectivity in the preceding degree and middle-term vanishing kill the kernel term. -/
theorem subsingleton_left_of_surjective (hS : S.ShortExact) (m n : ℕ)
    (hmn : m + 1 = n) (hsurj : Function.Surjective (map S.g m))
    [Subsingleton (H S.X₂ n)] : Subsingleton (H S.X₁ n) := by
  have hzero (x : H S.X₁ n) : x = 0 := by
    obtain ⟨z, hz⟩ := longSequence_exact₁ hS x (Subsingleton.elim _ _) hmn
    have he := (ShortComplex.ab_exact_iff_function_exact _).mp
      (longSequence_exact₃' hS m n hmn)
    exact hz.symm.trans ((he z).mpr (hsurj z))
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- Vanishing is preserved by a genuine extension of coefficient sheaves. -/
theorem subsingleton_middle_of_shortExact (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (H S.X₁ n)] [Subsingleton (H S.X₃ n)] :
    Subsingleton (H S.X₂ n) := by
  have hzero (x : H S.X₂ n) : x = 0 := by
    obtain ⟨y, hy⟩ := longSequence_exact₂ hS x (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end CategoryTheory.Sheaf.H
