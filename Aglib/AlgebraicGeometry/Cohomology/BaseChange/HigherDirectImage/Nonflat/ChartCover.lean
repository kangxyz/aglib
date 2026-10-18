/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # The covering family of all affine base-change chart pairs

For an arbitrary scheme morphism, affine chart pairs cover the target.
No quasi-compactness, flatness or Noetherian hypothesis is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {V X : Scheme.{u}}

/-- An actual pair of affine open charts with its original scalar map over `g`. -/
structure AffineBaseChangeChart (g : V ⟶ X) where
  /-- The coordinate ring of the source-base chart. -/
  sourceRing : CommRingCat.{u}
  /-- The coordinate ring of the target-base chart. -/
  targetRing : CommRingCat.{u}
  /-- The original source-base chart map. -/
  source : Spec sourceRing ⟶ X
  /-- The original target-base chart map. -/
  target : Spec targetRing ⟶ V
  /-- The original scalar map between these charts. -/
  scalar : sourceRing ⟶ targetRing
  /-- The source-base chart is open. -/
  source_open : IsOpenImmersion source
  /-- The target-base chart is open. -/
  target_open : IsOpenImmersion target
  /-- The affine chart pair lies over the actual scheme morphism. -/
  comm : Spec.map scalar ≫ source = target ≫ g

attribute [instance] AffineBaseChangeChart.source_open AffineBaseChangeChart.target_open

/-- All actual affine base-change chart pairs form a jointly covering family, for arbitrary
change of base and without a quasi-compactness condition on the new base. -/
theorem affineBaseChangeCharts_cover (g : V ⟶ X) (x : V) :
    ∃ (C : AffineBaseChangeChart g) (y : Spec C.targetRing), C.target y = x := by
  let U := X.affineOpenCover
  let W : V.OpenCover := U.openCover.pullback₁ g
  let Z : V.AffineOpenCover := W.affineRefinement
  let t := W.fromAffineRefinement
  let i := Z.openCover.idx x
  let k := t.s₀ i
  let r : Spec (Z.X i) ⟶ Spec (U.X k) := t.h₀ i ≫ U.openCover.pullbackHom g k
  have hr : r ≫ U.f k = Z.f i ≫ g := by
    dsimp only [r]
    erw [Category.assoc, Cover.pullbackHom_map, ← Category.assoc, t.w₀]
  let C : AffineBaseChangeChart g :=
    { sourceRing := U.X k
      targetRing := Z.X i
      source := U.f k
      target := Z.f i
      scalar := Spec.preimage r
      source_open := U.map_prop k
      target_open := Z.map_prop i
      comm := by rw [Spec.map_preimage]; exact hr }
  obtain ⟨y, hy⟩ := Z.openCover.covers x
  exact ⟨C, y, hy⟩

end AlgebraicGeometry.Scheme.Modules.Nonflat
