/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Abelian.Basic
public import Aglib.CategoryTheory.Preadditive.CoprimeScalar

/-! # Retracts from weak kernel closure

The original split inclusion is the kernel of the complementary idempotent.
Only a kernel of an endomorphism of a known object is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)
    [P.IsClosedUnderKernels]

/-- Weak kernel closure suffices for closure under actual retracts. -/
instance stableUnderRetracts_of_closedUnderKernels : P.IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    let a : Y ⟶ Y := 𝟙 Y - r.r ≫ r.i
    let k : KernelFork a := KernelFork.ofι r.i (by
      simp [a, Preadditive.comp_sub, ← Category.assoc, r.retract])
    have hk : IsLimit k := by
      apply Fork.IsLimit.mk _ (fun s => s.ι ≫ r.r)
      · intro s
        have hs : s.ι - (s.ι ≫ r.r) ≫ r.i = 0 := by
          simpa only [a, Preadditive.comp_sub, Category.comp_id, ← Category.assoc]
            using KernelFork.condition s
        exact (sub_eq_zero.mp hs).symm
      · intro s m hm
        change m ≫ r.i = s.ι at hm
        calc
          m = (m ≫ r.i) ≫ r.r := by
            rw [Category.assoc, r.retract]
            exact (Category.comp_id m).symm
          _ = s.ι ≫ r.r := by rw [hm]
    exact P.prop_of_isLimit_kernelFork hk hY hY

/-- Every functor retains the original coprime-trace retract, so any weak
kernel-closed target property descends along it without exactness assumptions. -/
theorem prop_obj_of_coprime_trace
    {D : Type*} [Category* D] [Preadditive D]
    {A B : D} (i : A ⟶ B) (t : B ⟶ A) (n p : ℕ)
    (ht : i ≫ t = n • 𝟙 A) (hcop : n.Coprime p) (hp : p • 𝟙 A = 0)
    (G : D ⥤ C) (hB : P (G.obj B)) : P (G.obj A) :=
  P.prop_of_retract ((Preadditive.retractOfCoprimeTrace i t n p ht hcop hp).map G) hB

end CategoryTheory.ObjectProperty
