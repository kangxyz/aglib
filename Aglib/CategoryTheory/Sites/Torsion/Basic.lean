/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Internal torsion of abelian presheaves

A section is locally torsion if its restrictions are annihilated by positive
integers on a covering sieve. The integer may vary over the cover. This is the
local condition used for torsion sheaves; it does not require a single
annihilator for a section on an arbitrary, possibly non-quasicompact object.
-/

@[expose] public noncomputable section

open Opposite

namespace CategoryTheory.Presheaf

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The sieve on which the original section has a positive annihilator. -/
def torsionSieve (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {U : C}
    (s : F.obj (op U)) : Sieve U where
  arrows V f := ∃ n : ℕ, 0 < n ∧ n • F.map f.op s = 0
  downward_closed := by
    intro V W f hf g
    obtain ⟨n, hn, hs⟩ := hf
    refine ⟨n, hn, ?_⟩
    have h := congrArg (F.map g.op) hs
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      map_nsmul, map_zero] using h

/-- The original section is locally killed by positive integers on a cover. -/
def IsLocallyTorsion (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (s : F.obj (op U)), torsionSieve F s ∈ J U

/-- A positive annihilator of the section makes its torsion sieve maximal. -/
theorem torsionSieve_eq_top_of_nsmul_eq_zero (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {U : C} (s : F.obj (op U)) {n : ℕ} (hn : 0 < n) (hs : n • s = 0) :
    torsionSieve F s = ⊤ := by
  apply top_unique
  intro V f _
  refine ⟨n, hn, ?_⟩
  simpa only [map_nsmul, map_zero] using congrArg (F.map f.op) hs

/-- Sectionwise torsion implies the internal local condition. -/
theorem isLocallyTorsion_of_sectionwise (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (h : ∀ (U : C) (s : F.obj (op U)), ∃ n : ℕ, 0 < n ∧ n • s = 0) :
    IsLocallyTorsion J F := by
  intro U s
  obtain ⟨n, hn, hs⟩ := h U s
  rw [torsionSieve_eq_top_of_nsmul_eq_zero F s hn hs]
  exact J.top_mem U

/-- An additive coefficient map preserves each section's original torsion sieve. -/
theorem torsionSieve_le_map {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : F ⟶ G)
    {U : C} (s : F.obj (op U)) :
    torsionSieve F s ≤ torsionSieve G (φ.app (op U) s) := by
  intro V f hf
  obtain ⟨n, hn, hs⟩ := hf
  refine ⟨n, hn, ?_⟩
  have h := congrArg (φ.app (op V)) hs
  simpa only [map_nsmul, map_zero, NatTrans.naturality_apply] using h

/-- Injective coefficient maps reflect the original torsion sieve of a section. -/
theorem torsionSieve_map_eq_of_injective {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (φ : F ⟶ G) (hφ : ∀ U, Function.Injective (φ.app U))
    {U : C} (s : F.obj (op U)) :
    torsionSieve G (φ.app (op U) s) = torsionSieve F s := by
  apply le_antisymm
  · intro V f hf
    obtain ⟨n, hn, hs⟩ := hf
    refine ⟨n, hn, hφ (op V) ?_⟩
    simpa only [map_nsmul, map_zero, NatTrans.naturality_apply] using hs
  · exact torsionSieve_le_map φ s

/-- Internal torsion passes to an actual coefficient subpresheaf. -/
theorem IsLocallyTorsion.of_injective {J : GrothendieckTopology C}
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (hG : IsLocallyTorsion J G)
    (φ : F ⟶ G) (hφ : ∀ U, Function.Injective (φ.app U)) :
    IsLocallyTorsion J F := by
  intro U s
  rw [← torsionSieve_map_eq_of_injective φ hφ s]
  exact hG U (φ.app (op U) s)

/-- A locally surjective coefficient map takes internally torsion objects to such objects. -/
theorem IsLocallyTorsion.of_isLocallySurjective {J : GrothendieckTopology C}
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (hF : IsLocallyTorsion J F)
    (φ : F ⟶ G) [IsLocallySurjective J φ] : IsLocallyTorsion J G := by
  intro U s
  apply J.transitive (imageSieve_mem J φ s)
  intro V f hf
  obtain ⟨t, ht⟩ := hf
  apply J.superset_covering ?_ (hF V t)
  intro W g hg
  obtain ⟨n, hn, hs⟩ := hg
  refine ⟨n, hn, ?_⟩
  have h := congrArg (φ.app (op W)) hs
  simpa only [map_nsmul, map_zero, NatTrans.naturality_apply, ht,
    op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply] using h

end CategoryTheory.Presheaf
