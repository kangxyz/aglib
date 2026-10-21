/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Dual.SplitInjection
public import Aglib.RingTheory.LocalRing.ProjectiveDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A degree-one Ext criterion for freeness

For a finite module of projective dimension at most one over a Noetherian
local ring, vanishing of `Ext¹(M,R)` makes the dual of a finite free resolution
surjective. Dual splitting and the native residue-field criterion yield
freeness, including the zero Ext-module branch of the dimension-three argument.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat

/-- A finite module of projective dimension at most one is free if its
first Ext into the ring vanishes. -/
theorem free_of_projectiveDimension_le_one_of_subsingleton_ext
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (hM : projectiveDimension M ≤ 1)
    [Subsingleton (Ext M (ModuleCat.of R R) 1)] : Module.Free R M := by
  obtain ⟨P₁, P₀, _, _, _, _, _, _, _, _, f, g, hf, hg, hex⟩ :=
    exists_finite_free_shortExact_of_projectiveDimension_le_one R M hM
  let S := ModuleCat.shortComplexOfCompEqZero f g hex.linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex hf hg
  have hdual : Function.Surjective f.dualMap := by
    intro φ
    obtain ⟨ξ, hξ⟩ := Ext.contravariant_sequence_exact₁ hS
      (ModuleCat.of R R) (Ext.mk₀ (ModuleCat.ofHom φ)) (by decide : 1 + 0 = 1)
      (Subsingleton.eq_zero _)
    obtain ⟨ψ, hψ⟩ := (Ext.mk₀_bijective S.X₂ (ModuleCat.of R R)).surjective ξ
    rw [← hψ, Ext.mk₀_comp_mk₀] at hξ
    have hcomp := (Ext.mk₀_bijective S.X₁ (ModuleCat.of R R)).injective hξ
    exact ⟨ψ.hom, congrArg ModuleCat.Hom.hom hcomp⟩
  obtain ⟨s, hs⟩ := f.exists_leftInverse_of_surjective_dualMap hdual
  exact Module.free_of_lTensor_residueField_injective f g hg hex
    ((IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mp ⟨s, hs⟩)

end ModuleCat
