/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sheaf cohomology of split short complexes

Every additive functor preserves a splitting of a short complex. For Mathlib's sheaf
cohomology `Sheaf.H` on an arbitrary site, a split short complex `0 → A → B → C → 0` of
abelian sheaves gives `H^n(B) ≃+ H^n(A) × H^n(C)` (`Sheaf.H.splittingAddEquiv`), with the
original retraction and second map as components. The kernel of `H^n(B) → H^n(C)` is
`H^n(A)` through the first map (`Sheaf.H.kerAddEquivOfSplitting`), and the first map is
injective on cohomology (`Sheaf.H.map_f_injective_of_splitting`). Sheafification and the Ext
universe remain explicit instance arguments.

The current consumer is the split square-zero unit sequence
(`Aglib.Algebra.Category.Ring.Sheaf.SquareZeroSplitting`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w z
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Generic

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{z} (Sheaf J AddCommGrpCat.{w})]

/-- The zero coefficient morphism induces zero on cohomology. -/
@[simp]
theorem H.map_zero_apply {F G : Sheaf J AddCommGrpCat.{w}} (n : ℕ) (x : H F n) :
    H.map (0 : F ⟶ G) n x = 0 := by
  rw [H.map_apply, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

variable {T : ShortComplex (Sheaf J AddCommGrpCat.{w})} (σ : T.Splitting) (n : ℕ)
include σ in
/-- The first map of a split short complex is injective on cohomology. -/
theorem H.map_f_injective_of_splitting : Function.Injective (H.map T.f n) := by
  intro x y hxy
  have h := congrArg (H.map σ.r n) hxy
  rwa [← H.map_comp_apply, ← H.map_comp_apply, σ.f_r, H.map_id_apply, H.map_id_apply] at h

/-- The composite of the two maps of a short complex is zero on cohomology. -/
theorem H.map_g_map_f (a : H T.X₁ n) : H.map T.g n (H.map T.f n a) = 0 := by
  rw [← H.map_comp_apply, T.zero, H.map_zero_apply]

/-- For a split short complex, a cohomology class of the middle term is the sum of the
images of its two components. -/
theorem H.map_f_map_r_add_map_s_map_g (x : H T.X₂ n) :
    H.map T.f n (H.map σ.r n x) + H.map σ.s n (H.map T.g n x) = x := by
  rw [← H.map_comp_apply, ← H.map_comp_apply, ← H.map_add_apply, σ.id, H.map_id_apply]

include σ in
/-- For a split short complex, the kernel of the second map on cohomology is the range
of the first map. -/
theorem H.map_g_eq_zero_iff_of_splitting (x : H T.X₂ n) :
    H.map T.g n x = 0 ↔ ∃ a : H T.X₁ n, H.map T.f n a = x := by
  constructor
  · intro hx
    refine ⟨H.map σ.r n x, ?_⟩
    have h := H.map_f_map_r_add_map_s_map_g σ n x
    rwa [hx, map_zero, add_zero] at h
  · rintro ⟨a, rfl⟩
    exact H.map_g_map_f n a

/-- A split short complex of abelian sheaves decomposes the cohomology of its middle term
as a product, with the original retraction and second map as components. -/
def H.splittingAddEquiv : H T.X₂ n ≃+ H T.X₁ n × H T.X₃ n where
  toFun x := (H.map σ.r n x, H.map T.g n x)
  invFun y := H.map T.f n y.1 + H.map σ.s n y.2
  left_inv x := H.map_f_map_r_add_map_s_map_g σ n x
  right_inv y := by
    obtain ⟨a, c⟩ := y
    refine Prod.ext ?_ ?_
    · change H.map σ.r n (H.map T.f n a + H.map σ.s n c) = a
      rw [map_add, ← H.map_comp_apply, ← H.map_comp_apply, σ.f_r, σ.s_r, H.map_id_apply,
        H.map_zero_apply, add_zero]
    · change H.map T.g n (H.map T.f n a + H.map σ.s n c) = c
      rw [map_add, ← H.map_comp_apply, ← H.map_comp_apply, T.zero, σ.s_g, H.map_id_apply,
        H.map_zero_apply, zero_add]
  map_add' x y := by
    change (H.map σ.r n (x + y), H.map T.g n (x + y)) =
      (H.map σ.r n x, H.map T.g n x) + (H.map σ.r n y, H.map T.g n y)
    rw [map_add, map_add]
    rfl

@[simp]
theorem H.splittingAddEquiv_apply (x : H T.X₂ n) :
    H.splittingAddEquiv σ n x = (H.map σ.r n x, H.map T.g n x) := rfl

@[simp]
theorem H.splittingAddEquiv_symm_apply (y : H T.X₁ n × H T.X₃ n) :
    (H.splittingAddEquiv σ n).symm y = H.map T.f n y.1 + H.map σ.s n y.2 := rfl

/-- For a split short complex of abelian sheaves, the kernel of the second map on
cohomology is the cohomology of the first term, through the original first map. -/
def H.kerAddEquivOfSplitting : (H.map T.g n).ker ≃+ H T.X₁ n where
  toFun x := H.map σ.r n x.1
  invFun a := ⟨H.map T.f n a, H.map_g_map_f n a⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    apply Subtype.ext
    change H.map T.f n (H.map σ.r n x) = x
    have h := H.map_f_map_r_add_map_s_map_g σ n x
    rwa [AddMonoidHom.mem_ker.mp hx, map_zero, add_zero] at h
  right_inv a := by
    change H.map σ.r n (H.map T.f n a) = a
    rw [← H.map_comp_apply, σ.f_r, H.map_id_apply]
  map_add' x y := map_add (H.map σ.r n) x.1 y.1

@[simp]
theorem H.kerAddEquivOfSplitting_symm_apply_coe (a : H T.X₁ n) :
    (((H.kerAddEquivOfSplitting σ n).symm a : (H.map T.g n).ker) : H T.X₂ n) =
      H.map T.f n a := rfl

end Generic

end CategoryTheory.Sheaf
