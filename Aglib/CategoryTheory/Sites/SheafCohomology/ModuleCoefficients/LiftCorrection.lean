/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Correcting a local lift by a degree-one primitive

A lift on the degree-zero term of an augmented resolution has a kernel-valued
obstruction in degree one. An actual primitive removes that obstruction, and
exactness of the original augmentation descends the corrected map. This is the
algebraic correction-and-gluing step, with every map retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A degree-one primitive corrects a degree-zero lift, which then descends along
the original augmentation. The conclusion supplies the actual lift of `h`. -/
theorem exists_lift_of_degreeOne_primitive
    (S D : ShortComplex C) (hS : S.ShortExact) (hD : D.Exact) [Epi D.g]
    {P₂ : C} (d₂ : P₂ ⟶ D.X₁) (hd₂ : d₂ ≫ D.f = 0)
    (hprim : ∀ (z : D.X₁ ⟶ S.X₁), d₂ ≫ z = 0 →
      ∃ (a : D.X₂ ⟶ S.X₁), D.f ≫ a = z)
    (h : D.X₃ ⟶ S.X₃) (b : D.X₂ ⟶ S.X₂) (hb : b ≫ S.g = D.g ≫ h) :
    ∃ (a : D.X₃ ⟶ S.X₂), a ≫ S.g = h := by
  let : Mono S.f := hS.mono_f
  have hbg : (D.f ≫ b) ≫ S.g = 0 := by
    rw [Category.assoc, hb, ← Category.assoc, D.zero, zero_comp]
  let z : D.X₁ ⟶ S.X₁ := hS.exact.lift (D.f ≫ b) hbg
  have hz : z ≫ S.f = D.f ≫ b := hS.exact.lift_f _ _
  have hdz : d₂ ≫ z = 0 := by
    apply (cancel_mono S.f).mp
    rw [Category.assoc, hz, ← Category.assoc, hd₂, zero_comp, zero_comp]
  obtain ⟨a, ha⟩ := hprim z hdz
  have hcorrected : D.f ≫ (b - a ≫ S.f) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, ha, hz, sub_self]
  refine ⟨hD.desc (b - a ≫ S.f) hcorrected, ?_⟩
  apply (cancel_epi D.g).mp
  rw [← Category.assoc, hD.g_desc, Preadditive.sub_comp, Category.assoc,
    S.zero, comp_zero, sub_zero, hb]

end CategoryTheory.Sheaf.ModuleCoefficients
