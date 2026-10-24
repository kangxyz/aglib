/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FinitePresentationLifting

/-! # Finite spans of local lifts of module generators

A locally surjective module-presheaf map lifts a finite module locally into a
finitely generated submodule of the original source sections. We do not claim
that its relations lift, or that a sheaf epimorphism is sectionwise surjective.
The submodule retains the original value universe even when the ring is larger.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Presheaf

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type r} [Ring R]

/-- Finitely many local generator lifts fit in a finite submodule of actual
source sections, after one common covering refinement. -/
theorem exists_cover_finite_span_lifts {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (η : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallySurjective J η]
    (M : ModuleCat.{w} R) [Module.Finite R M] {U : C} (g : M ⟶ G.obj (op U)) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
      ∃ P : Submodule R (F.obj (op V)), P.FG ∧
        ∀ m : M, ∃ p : P, η.app (op V) p = G.map f.op (g m) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  let π : (s →₀ R) →ₗ[R] M := Finsupp.linearCombination R Subtype.val
  have hπ : Function.Surjective π := LinearMap.range_eq_top.mp (by
    simpa [π, Finsupp.range_linearCombination] using hs)
  let T : J.Cover U := Finset.univ.inf (fun i : s =>
    ⟨CategoryTheory.Presheaf.imageSieve η (g i),
      CategoryTheory.Presheaf.imageSieve_mem J η (g i)⟩)
  refine ⟨T.1, T.2, ?_⟩
  intro V f hf
  have hfi (i : s) : CategoryTheory.Presheaf.imageSieve η (g i) f :=
    (show T ≤ (⟨_, CategoryTheory.Presheaf.imageSieve_mem J η (g i)⟩ : J.Cover U)
      from Finset.inf_le (Finset.mem_univ i)) f hf
  let b : s → F.obj (op V) := fun i => CategoryTheory.Presheaf.localPreimage η (g i) f (hfi i)
  let l := Finsupp.linearCombination R b
  let P := Submodule.span R (Set.range b)
  have hl : (η.app (op V)).hom ∘ₗ l = (G.map f.op).hom ∘ₗ g.hom ∘ₗ π := by
    ext i
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.linearCombination_single, one_smul, l, π]
    exact CategoryTheory.Presheaf.app_localPreimage η (g i) f (hfi i)
  refine ⟨P, Submodule.fg_def.mpr ⟨_, Set.finite_range b, rfl⟩, ?_⟩
  intro m
  obtain ⟨z, rfl⟩ := hπ m
  have hz : l z ∈ P := by
    change l z ∈ Submodule.span R (Set.range b)
    rw [← Finsupp.range_linearCombination]
    exact ⟨z, rfl⟩
  exact ⟨⟨l z, hz⟩, LinearMap.congr_fun hl z⟩

end ModuleCat.Presheaf
