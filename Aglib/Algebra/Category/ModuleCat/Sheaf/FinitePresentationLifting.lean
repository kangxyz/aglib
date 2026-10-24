/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Local lifting of maps from finitely presented modules

For a locally bijective morphism of module-valued presheaves, maps from a
finitely presented module lift locally. Finite generators first lift on a
common covering sieve, then finite relations vanish on a further covering
sieve. Descent through the actual presentation constructs the linear map.
This is a local statement, not global fullness of the constant sheaf functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Presheaf

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type r} [Ring R]

private theorem exists_common_cover {U : C} {ι : Type*} [Finite ι]
    (S : ι → Sieve U) (hS : ∀ i, S i ∈ J U) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ i, T ≤ S i := by
  classical
  let := Fintype.ofFinite ι
  let T : J.Cover U := Finset.univ.inf (fun i => ⟨S i, hS i⟩)
  refine ⟨T.1, T.2, fun i => ?_⟩
  exact (show T ≤ (⟨S i, hS i⟩ : J.Cover U) from
    Finset.inf_le (Finset.mem_univ i))

/-- Hom from a finitely presented module preserves local surjectivity of an
actual locally bijective morphism of module-valued presheaves. -/
theorem locallySurjective_coyoneda_of_finitePresentation
    {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (η : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallySurjective J η]
    [CategoryTheory.Presheaf.IsLocallyInjective J η]
    (M : ModuleCat.{w} R) [Module.FinitePresentation R M] :
    CategoryTheory.Presheaf.IsLocallySurjective J
      (Functor.whiskerRight η (coyoneda.obj (op M))) where
  imageSieve_mem {U} g := by
    classical
    change M ⟶ G.obj (op U) at g
    obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := R) (M := M)
    let π := Finsupp.linearCombination R ((↑) : s → M)
    have hπ : Function.Surjective π := LinearMap.range_eq_top.mp (by
      simpa [π, Finsupp.range_linearCombination] using hs)
    obtain ⟨S, hS, hSi⟩ := exists_common_cover J
      (fun i : s => CategoryTheory.Presheaf.imageSieve η (g i))
      (fun i => CategoryTheory.Presheaf.imageSieve_mem J η (g i))
    refine J.transitive hS
      (CategoryTheory.Presheaf.imageSieve
        (Functor.whiskerRight η (coyoneda.obj (op M))) g) ?_
    intro V f hf
    let b : s → F.obj (op V) := fun i =>
      CategoryTheory.Presheaf.localPreimage η (g i) f (hSi i _ hf)
    let l := Finsupp.linearCombination R b
    have hl : (η.app (op V)).hom ∘ₗ l = (G.map f.op).hom ∘ₗ g.hom ∘ₗ π := by
      ext i
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        Finsupp.linearCombination_single, one_smul, l, π]
      exact CategoryTheory.Presheaf.app_localPreimage η (g i) f (hSi i _ hf)
    have hrel (x : t) : η.app (op V) (l x) = η.app (op V) 0 := by
      have hx : π x = 0 := by
        apply (LinearMap.mem_ker).mp
        rw [← ht]
        exact Submodule.subset_span x.property
      change ((η.app (op V)).hom ∘ₗ l) x = _
      rw [hl]
      simp only [LinearMap.comp_apply, hx, map_zero]
    obtain ⟨T, hT, hTi⟩ := exists_common_cover J
      (fun x : t => CategoryTheory.Presheaf.equalizerSieve (l x) (0 : F.obj (op V)))
      (fun x => CategoryTheory.Presheaf.equalizerSieve_mem J η (l x) 0 (hrel x))
    refine J.superset_covering ?_ hT
    intro W k hk
    let l' := (F.map k.op).hom ∘ₗ l
    have hker : LinearMap.ker π ≤ LinearMap.ker l' := by
      rw [← ht, Submodule.span_le]
      intro x hx
      change F.map k.op (l x) = 0
      have heq := hTi (⟨x, hx⟩ : t) k hk
      simpa only [CategoryTheory.Presheaf.equalizerSieve_apply, map_zero] using heq
    let a : M →ₗ[R] F.obj (op W) :=
      (LinearMap.ker π).liftQ l' hker ∘ₗ
        (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap
    have ha : a ∘ₗ π = l' := by
      ext y
      simp [a, LinearMap.quotKerEquivOfSurjective_symm_apply]
    change ∃ a' : M ⟶ F.obj (op W),
      a' ≫ η.app (op W) = g ≫ G.map (k ≫ f).op
    refine ⟨ModuleCat.ofHom a, ?_⟩
    ext x
    obtain ⟨y, rfl⟩ := hπ x
    change η.app (op W) (a (π y)) = G.map (k ≫ f).op (g (π y))
    have hay : a (π y) = F.map k.op (l y) := LinearMap.congr_fun ha y
    have hly : η.app (op V) (l y) = G.map f.op (g (π y)) :=
      LinearMap.congr_fun hl y
    rw [hay, NatTrans.naturality_apply η k.op, hly]
    simp only [op_comp, G.map_comp, ModuleCat.comp_apply]

end ModuleCat.Presheaf
