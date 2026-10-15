/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # A displayed cokernel gives a zero-vertex pushout

Source:
`Quillen/Waldhausen/QuillenComparison/QuotientCalculus.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`942e8b7f327eddbf9c3cde6a7ff495297e8a27e398ff1ab706453073d9955e5d`.
Selected declarations: isPushoutOfZeroCokernel.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem isPushout_of_isColimit_cokernel {A B D Z : C} {i : A ⟶ B} {p : B ⟶ D}
    (w : i ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p w))
    (hZ : IsZero Z) (z : A ⟶ Z) (q : Z ⟶ D) : IsPushout i z p q := by
  have hsq : i ≫ p = z ≫ q := by rw [w, hZ.eq_of_src q 0, comp_zero]
  apply IsPushout.of_isColimit (c := PushoutCocone.mk p q hsq)
  refine PushoutCocone.IsColimit.mk hsq
    (fun s ↦ hp.desc (CokernelCofork.ofπ s.inl (by
      rw [s.condition, hZ.eq_of_src s.inr 0, comp_zero]))) ?_ ?_ ?_
  · intro s
    exact hp.fac _ WalkingParallelPair.one
  · intro s
    exact hZ.eq_of_src _ _
  · intro s m hm _
    apply Cofork.IsColimit.hom_ext hp
    change p ≫ m = p ≫ _
    rw [hm]
    symm
    exact hp.fac _ WalkingParallelPair.one

end CategoryTheory.Limits
