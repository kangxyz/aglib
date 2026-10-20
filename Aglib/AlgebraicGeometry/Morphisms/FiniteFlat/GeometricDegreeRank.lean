/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Fibres
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankOne
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Geometric degree determines native finite-etale rank

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Statements, chosen comparisons, and explicit incoming evidence boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.GeometricDegreeRank` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9ca1a980fb2b541c1e3157343b539febe95e46398915811813cb55244d420f5e`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.OverField (HasGeometricDegree)
universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- The original all-geometric-points degree determines native finite-flat
rank at every actual point. The geometric point used here is constructed from
that point's actual residue field and its algebraic closure. -/
theorem nativeRank_eq_of_hasGeometricDegree {F : Type u} [Field F]
    {X Y : FScheme F} (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (n : ℕ) (h : HasGeometricDegree f n) (y : Y.left) : f.left.finrank y = n := by
  let K := AlgebraicClosure (Y.left.residueField y)
  let p : Spec (.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
        Y.left.fromSpecResidueField y
  have hp : p default = y := by
    change Y.left.fromSpecResidueField y _ = y
    exact Scheme.fromSpecResidueField_apply _ _
  let s := p ≫ Y.hom
  let q : Over.mk s ⟶ Y := Over.homMk p rfl
  have hd := (hasGeometricFibreRank_iff_hasGeometricDegree f n).mpr h K s q
  rw [← hp, AlgebraicGeometry.Scheme.Hom.FiniteFlat.nativeRank_geometricFibre f.left K p]
  exact hd

end AlgebraicGeometry.Scheme.Hom
