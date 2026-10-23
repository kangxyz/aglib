/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Original cohomology maps with acyclic kernel and cokernel

All conclusions concern the literal original coefficient map on `Sheaf.H`.
No stalk identification or geometric support acyclicity is assumed implicitly.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Sheaf.H

universe c v a e

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}] [HasExt.{e} (Sheaf J AddCommGrpCat.{a})]

private theorem injective_of_exact_zero {A B D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] [Subsingleton A]
    (i : A →+ B) (p : B →+ D) (h : Function.Exact i p) :
    Function.Injective p := by
  intro x y hxy
  have hz : p (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (h (x - y)).mp hz
  apply sub_eq_zero.mp
  exact hz.symm.trans (by rw [Subsingleton.elim z 0, map_zero])

/-- The left map is bijective when the right term vanishes in the adjacent degrees. -/
theorem map_left_bijective_of_subsingleton
    {S : ShortComplex (Sheaf J AddCommGrpCat.{a})} (hS : S.ShortExact) (q : ℕ)
    [Subsingleton (H S.X₃ q)] [Subsingleton (H S.X₃ (q + 1))] :
    Function.Bijective (map S.f (q + 1)) := by
  constructor
  · exact injective_of_exact_zero (δ hS q (q + 1) rfl) (map S.f (q + 1))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (longSequence_exact₁' hS q (q + 1) rfl))
  · intro y
    exact longSequence_exact₂ hS y (Subsingleton.elim _ _)

/-- The right map is bijective when the left term vanishes in the adjacent degrees. -/
theorem map_right_bijective_of_subsingleton
    {S : ShortComplex (Sheaf J AddCommGrpCat.{a})} (hS : S.ShortExact) (q : ℕ)
    [Subsingleton (H S.X₁ q)] [Subsingleton (H S.X₁ (q + 1))] :
    Function.Bijective (map S.g q) := by
  constructor
  · exact injective_of_exact_zero (map S.f q) (map S.g q)
      ((ShortComplex.ab_exact_iff_function_exact _).mp (longSequence_exact₂' hS q))
  · intro y
    exact longSequence_exact₃ hS y rfl (Subsingleton.elim _ _)

/-- Four adjacent kernel/cokernel vanishings give bijectivity of the actual map. -/
theorem map_bijective_of_kernel_cokernel
    {F G : Sheaf J AddCommGrpCat.{a}} (f : F ⟶ G) (q : ℕ)
    [Subsingleton (H (kernel f) (q + 1))]
    [Subsingleton (H (kernel f) (q + 1 + 1))]
    [Subsingleton (H (cokernel f) q)]
    [Subsingleton (H (cokernel f) (q + 1))] :
    Function.Bijective (map f (q + 1)) := by
  let S₁ := ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (cokernel.condition _)
  have hS₁ : S₁.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι f) }
  have h₁ : Function.Bijective (map (Abelian.coimage.π f) (q + 1)) :=
    map_right_bijective_of_subsingleton hS₁ (q + 1)
  let S₂ := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _)
  have hS₂ : S₂.ShortExact := { exact := ShortComplex.exact_kernel (cokernel.π f) }
  have h₂ : Function.Bijective (map (Abelian.image.ι f) (q + 1)) :=
    map_left_bijective_of_subsingleton hS₂ q
  let e := Abelian.coimageIsoImage f
  have he : Function.Bijective (map e.hom (q + 1)) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨map e.inv (q + 1), ?_, ?_⟩
    · intro x
      rw [← map_comp_apply, e.hom_inv_id, map_id_apply]
    · intro x
      rw [← map_comp_apply, e.inv_hom_id, map_id_apply]
  have h := h₂.comp (he.comp h₁)
  have hfac : (fun x => map (Abelian.image.ι f) (q + 1)
      (map e.hom (q + 1) (map (Abelian.coimage.π f) (q + 1) x))) =
      map f (q + 1) := by
    funext x
    simp only [← map_comp_apply]
    exact congrArg (fun g => map g (q + 1) x) (Abelian.coimage_image_factorisation f)
  exact hfac ▸ h

end CategoryTheory.Sheaf.H
