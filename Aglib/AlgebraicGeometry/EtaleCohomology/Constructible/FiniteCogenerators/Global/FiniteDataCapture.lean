/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.ModuleImages
public import Aglib.RingTheory.FiniteType.SubalgebraColimit

/-! # Global module images capture original finite algebra stages

Actual affine finite-stage generator sets are simultaneously captured by
global finite-type quasicoherent module inclusions. Their original ranges
therefore contain those exact local stage subalgebras. Finite families have a
finite dependent generator index, as required by finite global realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open Scheme.Modules Scheme.Modules.QuasiCoherent

/-- Actual finite affine algebra generator sets are simultaneously captured by
one actual family of global finite-type QC module images. The original local
stage subalgebras are contained in the corresponding generated global charts.
For finite I the displayed dependent generator index is finite. -/
theorem exists_finiteType_images_containing_stages
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] {I : Type u}
    (U : I → X.affineOpens) (s : ∀ k, Finset Γ(Y, f ⁻¹ᵁ (U k).1)) :
    let J := Σ k, {x // x ∈ s k}
    ∃ (M : J → FiniteTypeSheaves X)
      (i : ∀ j, (M j).obj ⟶ pushforwardStructureSheaf f),
      (∀ j, Mono (i j)) ∧ ∀ k,
      letI := (f.app (U k).1).hom.toAlgebra
      Algebra.FiniteTypeSubalgebraLimit.stage Γ(X, (U k).1) Γ(Y, f ⁻¹ᵁ (U k).1) (s k) ≤
        Algebra.adjoin Γ(X, (U k).1)
          (sectionGenerators f (fun j => (M j).obj) i (U k).1) := by
  let J := Σ k, {x // x ∈ s k}
  obtain ⟨M, i, hi, hrange⟩ := exists_finiteType_images_of_sections f
    (fun j : J => U j.1) (fun j => j.2.val)
  refine ⟨M, i, hi, ?_⟩
  intro k
  let := (f.app (U k).1).hom.toAlgebra
  apply Algebra.adjoin_le
  intro x hx
  obtain ⟨m, hm⟩ := hrange ⟨k, ⟨x, hx⟩⟩
  exact Algebra.subset_adjoin
    (Set.mem_iUnion.mpr ⟨⟨k, ⟨x, hx⟩⟩, m, hm⟩)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
