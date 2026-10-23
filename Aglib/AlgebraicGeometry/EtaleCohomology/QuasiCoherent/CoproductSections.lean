/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.OverExtensive
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import Mathlib.CategoryTheory.Sites.Over

/-! # Sections on finite coproducts in the big étale slice

Finite coproduct inclusions are actual Zariski covers, also in the slice.
Consequently any sheaf for the original big étale slice topology preserves
finite products on the opposite category. No additional section sheaf is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme

/-- The extensive topology of the slice is contained in its original étale topology. -/
theorem extensiveTopology_le_etaleTopology_over (X : Scheme.{u}) :
    extensiveTopology (Over X) ≤ etaleTopology.over X := by
  apply ((Coverage.gi (Over X)).gc _ _).mpr
  rintro W R ⟨α, hα, Z, π, rfl, hπ⟩
  let : Finite α := hα
  let : IsIso (Sigma.desc π) := hπ
  change Sieve.ofArrows Z π ∈ (etaleTopology.over X) W
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply zariskiTopology_le_etaleTopology
  let c : Cofan Z := Cofan.mk W π
  have : IsIso (Sigma.desc c.inj) := by
    change IsIso (Sigma.desc π)
    exact hπ
  have hc : IsColimit c := Cofan.isColimitOfIsIsoSigmaDesc c
  have h := ofArrows_ι_mem_zariskiTopology_of_isColimit
    ((Discrete.functor Z) ⋙ Over.forget X)
    ((Over.forget X).mapCocone c) (isColimitOfPreserves (Over.forget X) hc)
  apply GrothendieckTopology.superset_covering _ _ h
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro Y f ⟨i⟩
  exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i.as)

/-- Original étale sheaves on a scheme slice send finite coproducts to products. -/
theorem preservesFiniteProducts_of_isSheaf_etale_over
    {D : Type v} [Category.{w} D] (X : Scheme.{u})
    (F : (Over X)ᵒᵖ ⥤ D) (hF : Presheaf.IsSheaf (etaleTopology.over X) F) :
    PreservesFiniteProducts F :=
  (Presheaf.isSheaf_iff_preservesFiniteProducts F).mp
    (hF.of_le (extensiveTopology_le_etaleTopology_over X))

end AlgebraicGeometry.Scheme
