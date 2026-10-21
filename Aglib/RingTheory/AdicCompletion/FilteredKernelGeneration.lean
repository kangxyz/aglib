/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemGenerators

/-!
# Finite filtration descent for ordinary relation modules

The filtration need not be the ideal-adic filtration. This is essential for
ordinary kernels of maps of adic systems. Spanning generators of its actual
successive quotients are lifted into a specified submodule, and finite descent
then puts the filtration tail inside that submodule. Nilpotent Nakayama finishes
the finite-level generation argument.
-/

@[expose] public noncomputable section

namespace Submodule

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Lift a spanning family in an actual filtered quotient into a submodule.
Every element of the filtration then lies in that submodule modulo the next
filtration term. Surjectivity or finite generation of the ambient module is
not assumed. -/
theorem le_sup_of_quotient_span_lifts (P P' Q : Submodule R M)
    {G : Type w} [AddCommGroup G] [Module R G] (q : P →ₗ[R] G)
    (hker : q.ker ≤ P'.comap P.subtype) (S : Set G)
    (hspan : span R S = ⊤)
    (hlift : ∀ s ∈ S, ∃ y : P, (y : M) ∈ Q ∧ q y = s) : P ≤ Q ⊔ P' := by
  have hs : span R S ≤ (Q.comap P.subtype).map q := by
    apply span_le.mpr
    intro s hs
    obtain ⟨y, hy, hqy⟩ := hlift s hs
    exact ⟨y, hy, hqy⟩
  intro x hx
  have hqx : q ⟨x, hx⟩ ∈ (Q.comap P.subtype).map q := by
    apply hs
    rw [hspan]
    exact mem_top
  obtain ⟨y, hy, hqy⟩ := hqx
  have hz : (⟨x, hx⟩ - y : P) ∈ q.ker := by
    change q (⟨x, hx⟩ - y) = 0
    rw [map_sub, hqy, sub_self]
  have hd : x - (y : M) ∈ P' := hker hz
  have hsum : (y : M) + (x - (y : M)) ∈ Q ⊔ P' :=
    Submodule.add_mem (Q ⊔ P') ((show Q ≤ Q ⊔ P' from le_sup_left) hy)
      ((show P' ≤ Q ⊔ P' from le_sup_right) hd)
  have he : (y : M) + (x - (y : M)) = x := by rw [add_comm, sub_add_cancel]
  rwa [he] at hsum

/-- A finite filtration tail is contained in `Q` if every successive term
is contained in `Q` modulo the next term. -/
theorem le_of_finite_filtration (L : ℕ → Submodule R M) (Q : Submodule R M)
    {m N : ℕ} (hmN : m ≤ N) (hN : L N ≤ Q)
    (hstep : ∀ j, m ≤ j → j < N → L j ≤ Q ⊔ L (j + 1)) : L m ≤ Q := by
  have h : ∀ j, j ≤ N → m ≤ j → L j ≤ Q := by
    intro j hj
    induction hj using Nat.decreasingInduction with
    | self => exact fun _ => hN
    | of_succ j hj ih =>
      intro hmj
      exact (hstep j hmj hj).trans (sup_le le_rfl (ih (Nat.le_succ_of_le hmj)))
  exact h m hmN le_rfl

/-- In particular, positive-ideal generation in every degree of a finite
filtration tail puts that entire tail in the ideal times the module. -/
theorem le_smul_top_of_finite_filtration (I : Ideal R)
    (L : ℕ → Submodule R M) {m N : ℕ} (hmN : m ≤ N) (hN : L N = ⊥)
    (hstep : ∀ j, m ≤ j → j < N → L j ≤ I • (⊤ : Submodule R M) ⊔ L (j + 1)) :
    L m ≤ I • (⊤ : Submodule R M) :=
  le_of_finite_filtration L _ hmN (by rw [hN]; exact bot_le) hstep

end Submodule

namespace LinearMap

universe u v w z

variable {R : Type u} [CommRing R]
  {P : Type v} [AddCommGroup P] [Module R P]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type z} [AddCommGroup N] [Module R N]

/-- A finite relation filtration with positive-ideal generated tail converts
generation at a fixed quotient into generation of the whole nilpotent stage.
No cartesian compatibility of the relation module is required. -/
theorem surjective_of_filtered_kernel (I : Ideal R) (g : P →ₗ[R] M)
    (t : M →ₗ[R] N) (htg : Function.Surjective (t.comp g))
    (L : ℕ → Submodule R M) {m k : ℕ} (hmk : m ≤ k)
    (hker : t.ker ≤ L m) (hk : L k = ⊥)
    (hstep : ∀ j, m ≤ j → j < k → L j ≤ I • (⊤ : Submodule R M) ⊔ L (j + 1))
    (e : ℕ) (he : I ^ e • (⊤ : Submodule R M) = ⊥) : Function.Surjective g :=
  surjective_of_surjective_comp_of_ker_le_smul I g t htg
    (hker.trans (Submodule.le_smul_top_of_finite_filtration I L hmk hk hstep)) e he

end LinearMap
