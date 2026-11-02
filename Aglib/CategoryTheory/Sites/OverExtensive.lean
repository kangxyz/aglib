/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.OverExtensive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
public import Mathlib.CategoryTheory.Sites.Over

/-! # Extensive coverings in the actual slice topology

The actual slice forgetful functor maps each finite colimit cofan to its
underlying colimit cofan, with the same legs. A base topology containing the
extensive topology therefore induces a slice topology containing the extensive
topology of that slice. Finite families may be empty.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits

universe u v

variable {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]

/-- Actual finite coproduct covers remain covers in the induced slice topology. -/
theorem extensiveTopology_le_over (J : GrothendieckTopology C)
    (hJ : extensiveTopology C ≤ J) (X : C) [FinitaryPreExtensive (Over X)] :
    extensiveTopology (Over X) ≤ J.over X := by
  apply ((Coverage.gi (Over X)).gc _ _).mpr
  rintro W R ⟨α, hα, Z, π, rfl, hπ⟩
  let : Finite α := hα
  let : IsIso (Sigma.desc π) := hπ
  change Sieve.ofArrows Z π ∈ (J.over X) W
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply hJ
  apply (extensiveTopology.mem_sieves_iff_contains_colimit_cofan _).mpr
  let c : Cofan Z := Cofan.mk W π
  have : IsIso (Sigma.desc c.inj) := by
    change IsIso (Sigma.desc π)
    exact hπ
  have hc : IsColimit c := Cofan.isColimitOfIsIsoSigmaDesc c
  refine ⟨α, hα, (fun i => (Z i).left), (fun i => (π i).left), ?_, ?_⟩
  · exact ⟨isColimitCofanMkObjOfIsColimit (Over.forget X) Z π hc⟩
  · intro i
    exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i)

end CategoryTheory
