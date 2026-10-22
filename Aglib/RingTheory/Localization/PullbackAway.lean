/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localized isomorphisms in cartesian ring squares

If one side of a cartesian square of commutative rings becomes an isomorphism
on a specified principal open, then the opposite side does too. The maps are
the native localization maps of the original square (Stacks 01Z9's algebraic step).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace IsLocalization.Away

universe u

/-- Bijectivity of one localized map in an actual cartesian ring square gives
bijectivity of the opposite localized map. No flatness or Noetherianity is assumed. -/
theorem map_bijective_of_isPullback
    {A B C D : CommRingCat.{u}} (p : A ⟶ B) (q : A ⟶ C)
    (s : B ⟶ D) (t : C ⟶ D) (H : IsPullback p q s t) (h : A)
    (hs : Function.Bijective (map (Localization.Away (p.hom h))
      (Localization.Away (s.hom (p.hom h))) s.hom (p.hom h))) :
    Function.Bijective (map (Localization.Away h)
      (Localization.Away (q.hom h)) q.hom h) := by
  have HT := Functor.map_isPullback (forget CommRingCat.{u}) H
  have hw (x : A) : s.hom (p.hom x) = t.hom (q.hom x) :=
    congrArg (fun f : A ⟶ D ↦ f.hom x) H.w
  constructor
  · apply (map_injective_iff (Localization.Away (q.hom h)) q.hom h).mpr
    intro a ha
    have hsa : s.hom (p.hom a) = 0 := by rw [hw, ha, map_zero]
    obtain ⟨n, hn⟩ :=
      (map_injective_iff (Localization.Away (s.hom (p.hom h))) s.hom (p.hom h)).mp
        hs.1 (p.hom a) hsa
    refine ⟨n, Types.ext_of_isPullback HT ?_ ?_⟩
    · change p.hom (h ^ n * a) = p.hom 0
      simpa only [map_mul, map_pow, map_zero] using hn
    · change q.hom (h ^ n * a) = q.hom 0
      simp only [map_mul, map_pow, ha, mul_zero, map_zero]
  · apply (map_surjective_iff (Localization.Away h)
      (Localization.Away (q.hom h)) q.hom h).mpr
    intro c
    obtain ⟨b, n, hb⟩ :=
      (map_surjective_iff (Localization.Away (p.hom h))
        (Localization.Away (s.hom (p.hom h))) s.hom (p.hom h)).mp hs.2 (t.hom c)
    have he : s.hom b = t.hom (q.hom h ^ n * c) := by
      rw [map_mul, map_pow, ← hw, hb]
    obtain ⟨a, -, ha⟩ := Types.exists_of_isPullback HT b (q.hom h ^ n * c) he
    exact ⟨a, n, ha⟩

end IsLocalization.Away
