/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SquarePasting

/-!
# A finite coherence chase for exchange squares

This categorical calculation factors three associativity comparisons and two
transport squares before specializing to geometric or derived functors.
-/

@[expose] public section
namespace CategoryTheory

variable {C : Type*} [Category* C]
  {A B C₀ D E F G H I J K L M N O : C}
  {p : A ⟶ B} {q : B ⟶ C₀} {b₀ : C₀ ⟶ D} {t₂ : D ⟶ E}
  {c₀ : E ⟶ F} {d : G ≅ F} {t₁ : G ⟶ H} {e₀ : H ⟶ I}
  {a : A ⟶ J} {m : J ⟶ D} {b : J ⟶ K} {n : K ⟶ E}
  {c : K ⟶ L} {r : L ⟶ G} {e : L ⟶ M} {s : M ⟶ H}
  {z : M ⟶ N} {u : N ⟶ O} {v : O ⟶ I} {τ : A ⟶ N}

/-- The exchange chase is formal once its actual five comparison equations are supplied. -/
theorem exchangeCoherence_chain
    (h₁ : p ≫ q ≫ b₀ = a ≫ m)
    (h₂ : m ≫ t₂ = b ≫ n)
    (h₃ : n ≫ c₀ = c ≫ r ≫ d.hom)
    (h₄ : r ≫ t₁ = e ≫ s)
    (h₅ : s ≫ e₀ = z ≫ u ≫ v)
    (ht : a ≫ b ≫ c ≫ e ≫ z = τ) :
    p ≫ q ≫ b₀ ≫ t₂ ≫ c₀ ≫ d.inv ≫ t₁ ≫ e₀ = τ ≫ u ≫ v := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% h₄, h₅]
  rw [reassoc_of% ht]

end CategoryTheory
