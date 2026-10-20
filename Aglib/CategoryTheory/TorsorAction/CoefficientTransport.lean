/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.TorsorAction.Basic

/-!
# Transport of a universal kernel marking along a coefficient isomorphism

Only the coefficient changes. The source, target and actual group
morphism remain fixed, and the new inclusion is the specified inverse
coefficient isomorphism followed by the original inclusion. This uses the
same universal property on every object of an arbitrary Cartesian category.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.Kernel.Remarking`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`665948b0e062bd71557b3c956f09a9cb918e4110cf16d14588d7d28d65463f04`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.KernelMarking

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A A' G H : Grp C} {p : G ⟶ H}
  (m : KernelMarking A G H p) (e : A ≅ A')

def transportCoefficient : KernelMarking A' G H p where
  inclusion := e.inv ≫ m.inclusion
  over := by
    change (e.inv.hom.hom ≫ m.inclusion.hom.hom) ≫ p.hom.hom = _
    rw [Category.assoc, m.over, MonObj.comp_one]
  unique_lift k hk := by
    obtain ⟨a, ha, hu⟩ := m.unique_lift k hk
    have hei : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 A.X :=
      congrArg (fun z : A ⟶ A => z.hom.hom) e.hom_inv_id
    have hie : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 A'.X :=
      congrArg (fun z : A' ⟶ A' => z.hom.hom) e.inv_hom_id
    refine ⟨a ≫ e.hom.hom.hom, ?_, ?_⟩
    · change (a ≫ e.hom.hom.hom) ≫ (e.inv.hom.hom ≫ m.inclusion.hom.hom) = k
      rw [Category.assoc, ← Category.assoc e.hom.hom.hom, hei, Category.id_comp, ha]
    · intro b hb
      have hba : b ≫ e.inv.hom.hom = a := hu _ (by
        change b ≫ (e.inv.hom.hom ≫ m.inclusion.hom.hom) = k at hb
        simpa only [Category.assoc] using hb)
      rw [← hba, Category.assoc, hie, Category.comp_id]

end CategoryTheory.KernelMarking
