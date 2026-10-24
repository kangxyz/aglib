/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # A cokernel presentation of an extension from lifted quotient generators

For an actual short exact sequence, a map to its middle term whose composite
with the quotient is epic gives a presentation of the middle term. The
relations are the kernel of that quotient composite. No splitting or
projectivity of the auxiliary source is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.ShortComplex.ShortExact

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Lifted quotient generators give a genuine cokernel presentation of the
middle object, with relations equal to the kernel of the quotient composite. -/
theorem exists_cokernel_presentation {S : ShortComplex C} (hS : S.ShortExact)
    {P : C} (v : P ⟶ S.X₂) [Epi (v ≫ S.g)] :
    ∃ a : kernel (v ≫ S.g) ⟶ S.X₁ ⊞ P, Nonempty (cokernel a ≅ S.X₂) := by
  let := hS.mono_f
  let := hS.epi_g
  let k := kernel.ι (v ≫ S.g)
  have hkv : (k ≫ v) ≫ S.g = 0 := by simp [k, Category.assoc]
  let t := hS.exact.lift (k ≫ v) hkv
  have htf : t ≫ S.f = k ≫ v := hS.exact.lift_f _ _
  let a : kernel (v ≫ S.g) ⟶ S.X₁ ⊞ P := biprod.lift (-t) k
  let q : S.X₁ ⊞ P ⟶ S.X₂ := biprod.desc S.f v
  have haq : a ≫ q = 0 := by simp [a, q, htf]
  have hqg : q ≫ S.g = biprod.snd ≫ v ≫ S.g := by
    apply biprod.hom_ext' <;> simp [q, S.zero]
  let : Epi q := epi_of_cancel_zero q (fun {Z} z hz => by
    have hfz : S.f ≫ z = 0 := by
      simpa [q] using congrArg (fun b => biprod.inl ≫ b) hz
    obtain ⟨d, hd⟩ := hS.exact.desc' z hfz
    have hvz : v ≫ z = 0 := by
      simpa [q] using congrArg (fun b => biprod.inr ≫ b) hz
    have hd0 : d = 0 := (cancel_epi (v ≫ S.g)).mp (by simpa [Category.assoc, hd] using hvz)
    simpa [hd0] using hd.symm)
  let : Mono a := mono_of_mono_fac (show a ≫ biprod.snd = k by simp [a])
  let hker : IsLimit (KernelFork.ofι a haq) := KernelFork.IsLimit.ofι' a haq (by
    intro Z b hb
    have hbg : (b ≫ biprod.snd) ≫ (v ≫ S.g) = 0 := by
      rw [Category.assoc, ← hqg, ← Category.assoc, hb, zero_comp]
    let l := kernel.lift (v ≫ S.g) (b ≫ biprod.snd) hbg
    have hl : l ≫ k = b ≫ biprod.snd := kernel.lift_ι _ _ _
    refine ⟨l, ?_⟩
    apply biprod.hom_ext
    · apply (cancel_mono S.f).mp
      have hb' : (b ≫ biprod.fst) ≫ S.f + (b ≫ biprod.snd) ≫ v = 0 := by
        simpa [q, biprod.desc_eq, Category.assoc, comp_add] using hb
      calc
        ((l ≫ a) ≫ biprod.fst) ≫ S.f = -(l ≫ (t ≫ S.f)) := by
          simp [a, Category.assoc]
        _ = -((b ≫ biprod.snd) ≫ v) := by rw [htf, ← Category.assoc, hl]
        _ = (b ≫ biprod.fst) ≫ S.f := (eq_neg_of_add_eq_zero_left hb').symm
    · simpa [a] using hl)
  exact ⟨a, ⟨(colimit.isoColimitCocone
    ⟨_, Abelian.epiIsCokernelOfKernel _ hker⟩)⟩⟩

end CategoryTheory.ShortComplex.ShortExact
