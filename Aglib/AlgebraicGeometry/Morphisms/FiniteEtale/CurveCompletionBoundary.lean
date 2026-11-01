/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CurveCompletion
public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Aglib.AlgebraicGeometry.Dimension.DenseOpenComplement

/-! # Finite proper curve completion with its actual zero-dimensional boundary

This assembles the canonical finite completion, dimension monotonicity for
its actual finite map, and a closed complement of its dense original open.
It retains the original field, cover, base, and Cartesian square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Every finite-etale cover of an open of a proper integral field curve has
an actual finite proper completion of dimension at most one, together with
its original Cartesian open restriction and a zero-dimensional closed boundary.
No normality, perfectness, connectedness or nonemptiness of the cover is assumed. -/
theorem exists_finite_proper_completion_with_boundary_of_fieldCurve
    {k : Type u} [Field k] {V U X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1)
    (v : V ⟶ U) [IsFinite v] [Etale v]
    (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ (Y : Scheme.{u}) (j' : V ⟶ Y) (b : Y ⟶ X),
      IsOpenImmersion j' ∧ IsDominant j' ∧ IsFinite b ∧
        IsProper (b ≫ p) ∧ topologicalKrullDim Y ≤ 1 ∧ IsPullback j' v b j ∧
        ∃ (D : Scheme.{u}) (i : D ⟶ Y), IsClosedImmersion i ∧
          Set.range j' = (Set.range i)ᶜ ∧ topologicalKrullDim D ≤ 0 := by
  obtain ⟨Y, j', b, hj', hdense, hb, hp, H⟩ :=
    exists_finite_proper_completion_of_fieldCurve p hdim v j
  let := hj'
  let := hdense
  let := hb
  let := hp
  have hY : topologicalKrullDim Y ≤ 1 := b.topologicalKrullDim_le_of_isFinite.trans hdim
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (b ≫ p)
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (b ≫ p)
  let : IsNoetherian Y := ⟨⟩
  obtain ⟨D, i, hi, hcomp, hD⟩ :=
    j'.exists_closedComplement_topologicalKrullDim_le 0 (by simpa using hY)
  exact ⟨Y, j', b, hj', hdense, hb, hp, hY, H, D, i, hi, hcomp, by simpa using hD⟩

end AlgebraicGeometry.Scheme
