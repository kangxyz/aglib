/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Limits of original kernel cones

Compatible kernel forks at the original cone vertices and diagram stages
transfer the limit property from the two right cones to the left cone.
Only the supplied native lifts are used; no replacement limit is selected.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u vJ uJ

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {J : Type uJ} [Category.{vJ} J]
  {F G H : J ⥤ C} (i : F ⟶ G) (g : G ⟶ H)
  (w : ∀ j, i.app j ≫ g.app j = 0)
  (cF : Cone F) (cG : Cone G) (cH : Cone H)
  (a : cF.pt ⟶ cG.pt) (b : cG.pt ⟶ cH.pt) (wab : a ≫ b = 0)
  (ha : ∀ j, a ≫ cG.π.app j = cF.π.app j ≫ i.app j)
  (hb : ∀ j, b ≫ cH.π.app j = cG.π.app j ≫ g.app j)

include ha hb in
/-- Original stage kernels and the original vertex kernel preserve the limit cone. -/
def isLimitOfKernelCones
    (h₀ : IsLimit (KernelFork.ofι a wab))
    (hstage : ∀ j, IsLimit (KernelFork.ofι (i.app j) (w j)))
    (hG : IsLimit cG) (hH : IsLimit cH) : IsLimit cF := by
  let : Mono a := mono_of_isLimit_fork h₀
  let liftData (s : Cone F) :
      { m : s.pt ⟶ cF.pt // ∀ j, m ≫ cF.π.app j = s.π.app j } := by
    let sG : Cone G := ⟨s.pt, s.π ≫ i⟩
    let z := hG.lift sG
    have hfac (j : J) : z ≫ cG.π.app j = s.π.app j ≫ i.app j := by
      simpa only [sG, NatTrans.comp_app] using hG.fac sG j
    have hz : z ≫ b = 0 := by
      apply hH.hom_ext
      intro j
      calc
        (z ≫ b) ≫ cH.π.app j = (z ≫ cG.π.app j) ≫ g.app j := by
          rw [Category.assoc, hb j, ← Category.assoc]
        _ = (s.π.app j ≫ i.app j) ≫ g.app j := by rw [hfac j]
        _ = 0 := by rw [Category.assoc, w j, comp_zero]
        _ = 0 ≫ cH.π.app j := by simp only [zero_comp]
    let l := KernelFork.IsLimit.lift' h₀ z hz
    have hl : l.val ≫ a = z := l.property
    refine ⟨l.val, ?_⟩
    intro j
    let : Mono (i.app j) := mono_of_isLimit_fork (hstage j)
    apply (cancel_mono (i.app j)).mp
    calc
      (l.val ≫ cF.π.app j) ≫ i.app j = (l.val ≫ a) ≫ cG.π.app j := by
        rw [Category.assoc, ← ha j, ← Category.assoc]
      _ = z ≫ cG.π.app j := by rw [hl]
      _ = s.π.app j ≫ i.app j := hfac j
  refine ⟨fun s => (liftData s).val, fun s j => (liftData s).property j, ?_⟩
  intro s m hm
  apply (cancel_mono a).mp
  apply hG.hom_ext
  intro j
  calc
    (m ≫ a) ≫ cG.π.app j = (m ≫ cF.π.app j) ≫ i.app j := by
      rw [Category.assoc, ha j, ← Category.assoc]
    _ = s.π.app j ≫ i.app j := by rw [hm j]
    _ = ((liftData s).val ≫ cF.π.app j) ≫ i.app j := by
      rw [(liftData s).property j]
    _ = ((liftData s).val ≫ a) ≫ cG.π.app j := by
      rw [Category.assoc, ← ha j, ← Category.assoc]

end CategoryTheory.Limits
