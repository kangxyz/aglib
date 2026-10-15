/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
/-! # Isomorphisms are admissible in an exact category -/
@[expose] public section


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- Every isomorphism is an admissible monomorphism, since it is a kernel of
an admissible zero map to zero. -/
lemma inflation_of_iso {X Y : C} (e : X ≅ Y) : E.inflation e.hom := by
  apply E.inflation_of_isKernel (p := (0 : Y ⟶ 0)) (by simp) _ (E.deflation_zero Y)
  refine KernelFork.IsLimit.ofι e.hom (by simp)
    (fun g _ => g ≫ e.inv) (fun g _ => by simp) ?_
  intro W g _ m hm
  rw [← hm]
  simp

/-- Every isomorphism is an admissible epimorphism, by the dual cokernel argument. -/
lemma deflation_of_iso {X Y : C} (e : X ≅ Y) : E.deflation e.hom := by
  apply E.deflation_of_isCokernel (i := (0 : 0 ⟶ X)) (by simp) _ (E.inflation_zero X)
  refine CokernelCofork.IsColimit.ofπ e.hom (by simp)
    (fun g _ => e.inv ≫ g) (fun g _ => by simp) ?_
  intro W g _ m hm
  rw [← hm]
  simp

end CategoryTheory.ExactCategory.ExactStructure
