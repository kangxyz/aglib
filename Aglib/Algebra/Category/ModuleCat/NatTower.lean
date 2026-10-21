/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Types.NatTower
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Original evaluation maps of module-valued natural-number towers

The native compatible-section submodule projects surjectively to every stage
when the adjacent maps are surjective. Ring and carrier universes are independent.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R] (F : ℕᵒᵖ ⥤ ModuleCat.{v} R)

/-- Evaluation at an original stage, on the native compatible-section submodule. -/
def sectionsEval (n : ℕ) : sectionsSubmodule F →ₗ[R] F.obj (op n) where
  toFun s := s.val (op n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sectionsEval_apply (n : ℕ) (s : sectionsSubmodule F) :
    sectionsEval F n s = s.val (op n) := rfl

/-- Evaluation commutes with every original transition, not only adjacent ones. -/
theorem map_sectionsEval {m n : ℕ} (h : m ≤ n) (s : sectionsSubmodule F) :
    F.map (homOfLE h).op (sectionsEval F n s) = sectionsEval F m s :=
  s.property (homOfLE h).op

/-- Surjective adjacent maps make every native evaluation surjective. -/
theorem sectionsEval_surjective
    (h : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (n : ℕ) : Function.Surjective (sectionsEval F n) :=
  (F ⋙ forget (ModuleCat R)).sections_eval_surjective_of_surjective_succ h n

end ModuleCat
