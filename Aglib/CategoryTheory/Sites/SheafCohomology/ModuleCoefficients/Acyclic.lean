/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# A dimension-shifting criterion for acyclicity

This criterion uses surjectivity in degree zero and stability under injective
cokernels. Neither hypothesis assumes any positive Ext vanishing.
It applies to the original Ext groups, in any supplied Ext universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] [EnoughInjectives C]

/-- A class closed under injective cokernels is acyclic if Hom from `X` is
surjective on the corresponding short exact sequences. -/
theorem eq_zero_of_cokernel_stable (X : C) (P : C → Prop)
    (hquot : ∀ (S : ShortComplex C), S.ShortExact → Injective S.X₂ → P S.X₁ → P S.X₃)
    (hsurj : ∀ (S : ShortComplex C), S.ShortExact → Injective S.X₂ → P S.X₁ →
      Function.Surjective (fun a : X ⟶ S.X₂ => a ≫ S.g))
    {Y : C} (hY : P Y) (n : ℕ) (x : Ext.{w} X Y (n + 1)) : x = 0 := by
  classical
  induction n generalizing Y with
  | zero =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨z, hz⟩ := covariant_sequence_exact₁ X hS x (eq_zero_of_injective _) rfl
    obtain ⟨a, ha⟩ := hsurj S hS inferInstance hY (homEquiv₀ z)
    change a ≫ S.g = homEquiv₀ z at ha
    have hza : mk₀ (a ≫ S.g) = z := by
      rw [ha]
      exact mk₀_homEquiv₀_apply z
    rw [← hz, ← hza, ← mk₀_comp_mk₀, comp_assoc_of_second_deg_zero,
      hS.comp_extClass, comp_zero]
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨z, hz⟩ := covariant_sequence_exact₁ X hS x (eq_zero_of_injective _) rfl
    rw [← hz, ih (hquot S hS inferInstance hY) z, zero_comp]

end CategoryTheory.Abelian.Ext
