/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.SizeBound
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The downward exactness step for a small acyclic subcomplex

Given an exact short complex and a restricted second differential, a small
subobject of its first term can be chosen to cover the cycles of the restricted
differential. The resulting restricted short complex is exact. The cardinal
bound is uniform in the ambient short complex and all its objects and maps.

This is the one-degree induction step in Stacks 079K, using the cardinal
lifting construction of Stacks 079J. It is not yet an acyclic complex or a
K-injective existence theorem.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

include hG

/-- A size-controlled exactness step for a restricted differential.
The actual monomorphism `i` into the first ambient term and the epimorphism
`e` onto the restricted cycles retain the original differential equation.
No monicity assumption on `b` is needed for this construction. -/
lemma exists_regular_cardinal_exact_step (κ : Cardinal.{w}) :
    ∃ μ : Cardinal.{w}, μ.IsRegular ∧
      ∀ (S : ShortComplex C), S.Exact →
        ∀ {A B : C} (a : A ⟶ S.X₂) [Mono a] (b : B ⟶ S.X₃) (δ : A ⟶ B),
          δ ≫ b = a ≫ S.g → HasCardinalLT (Subobject A) κ →
          ∃ (X : C) (i : X ⟶ S.X₁) (e : X ⟶ kernel δ),
            Mono i ∧ Epi e ∧ i ≫ S.f = e ≫ kernel.ι δ ≫ a ∧
              HasCardinalLT (Subobject X) μ ∧
              (ShortComplex.mk (e ≫ kernel.ι δ) δ (by simp)).Exact := by
  obtain ⟨μ, hμ, hbound⟩ := exists_regular_cardinal_lifting_bound hG κ
  refine ⟨μ, hμ, ?_⟩
  intro S hS A B a ha b δ hδ hA
  let q : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  have : Epi q := hS.epi_kernelLift
  have hz₀ : (kernel.ι δ ≫ a) ≫ S.g = 0 := by
    rw [Category.assoc, ← hδ, ← Category.assoc, kernel.condition, zero_comp]
  let z : kernel δ ⟶ kernel S.g := kernel.lift S.g (kernel.ι δ ≫ a) hz₀
  have hz : z ≫ kernel.ι S.g = kernel.ι δ ≫ a := by simp [z]
  have : Mono z := mono_of_mono_fac hz
  have hker : HasCardinalLT (Subobject (kernel δ)) κ :=
    Subobject.hasCardinalLT_of_mono hA (kernel.ι δ)
  have hker' : Cardinal.mk (Shrink.{w} (Subobject (kernel δ))) ≤ κ := by
    have h := (hasCardinalLT_iff_of_equiv
      (equivShrink.{w} (Subobject (kernel δ))) κ).1 hker
    exact ((hasCardinalLT_iff_cardinal_mk_lt _ _).1 h).le
  obtain ⟨U, hU, hsize⟩ := hbound (pullback.snd q z) hker'
  have := hU
  let i : (U : C) ⟶ S.X₁ := U.arrow ≫ pullback.fst q z
  let e : (U : C) ⟶ kernel δ := U.arrow ≫ pullback.snd q z
  refine ⟨(U : C), i, e, inferInstance, hU, ?_, hsize, ?_⟩
  · change (U.arrow ≫ pullback.fst q z) ≫ S.f =
      (U.arrow ≫ pullback.snd q z) ≫ kernel.ι δ ≫ a
    calc
      (U.arrow ≫ pullback.fst q z) ≫ S.f =
          U.arrow ≫ (pullback.fst q z ≫ q) ≫ kernel.ι S.g := by simp [q]
      _ = U.arrow ≫ (pullback.snd q z ≫ z) ≫ kernel.ι S.g := by
        rw [pullback.condition]
      _ = (U.arrow ≫ pullback.snd q z) ≫ kernel.ι δ ≫ a := by
        simp only [Category.assoc, hz]
  · apply (ShortComplex.exact_iff_epi_kernel_lift _).2
    have he : kernel.lift δ (e ≫ kernel.ι δ) (by simp) = e := by
      apply (cancel_mono (kernel.ι δ)).1
      simp
    rw [he]
    exact hU

end CategoryTheory.IsGrothendieckAbelian
