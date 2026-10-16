/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension from an actual finite resolution

An actual zero term of a supplied native projective resolution kills the
corresponding native Ext group. A finite support bound therefore gives the
existing projective-dimension bound, without choosing another resolution or
requiring enough projectives in the ambient category. The regular-sequence
Koszul resolution is the immediate consumer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v w

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w} C] {X : C} (P : ProjectiveResolution X)

/-- A zero term of the original supplied resolution kills every native Ext
class in that same degree, for arbitrary coefficient objects and Ext universes. -/
theorem ext_eq_zero_of_isZero_X {Y : C} (n : ℕ)
    (hn : IsZero (P.complex.X n)) (e : Ext X Y n) : e = 0 := by
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hzero : f = 0 := hn.eq_of_src _ _
  subst f
  exact P.extMk_zero (n + 1) rfl

omit [HasExt.{w} C] in
/-- The finite support of an actual supplied projective resolution gives
its source the native projective-dimension bound. -/
theorem hasProjectiveDimensionLE_of_isZero_X (n : ℕ)
    (hP : ∀ i : ℕ, n < i → IsZero (P.complex.X i)) :
    HasProjectiveDimensionLE X n := by
  let := HasExt.standard C
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  exact P.ext_eq_zero_of_isZero_X i (hP i (by omega)) e

end CategoryTheory.ProjectiveResolution
