/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.IntegralBaseChange
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Original model localization at a target stalk

The literal pullback along the original target stalk spectrum is integral
for a dominant map of integral schemes. Its first projection is dominant,
and its actual stalk isomorphisms preserve normality. A closed original
source point has a closed lift with both prescribed projections.
No properness, finiteness, Noetherianity or surface hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The original first projection from a target-stalk localization is
 dominant, witnessed by a genuine lift of the original generic point. -/
theorem isDominant_pullback_fst_fromSpecStalk
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] (x : X) :
    IsDominant (pullback.fst p (X.fromSpecStalk x)) := by
  let s := X.fromSpecStalk x
  have hg : genericPoint X ∈ Set.range s := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  obtain ⟨t, ht⟩ := hg
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (genericPoint Y) t
    ((Scheme.map_genericPoint_of_isDominant Y p).trans ht.symm)
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨z, hz⟩)

/-- A closed original source point lifts to a closed point of the literal
model localization, retaining both original projection equations. -/
theorem exists_closed_point_pullback_fromSpecStalk
    {Y X : Scheme.{u}} (p : Y ⟶ X) (y : Y) (x : X) (hpx : p y = x)
    (hy : IsClosed ({y} : Set Y)) :
    ∃ z : (pullback p (X.fromSpecStalk x) : Scheme.{u}),
      pullback.fst p (X.fromSpecStalk x) z = y ∧
      pullback.snd p (X.fromSpecStalk x) z = IsLocalRing.closedPoint (X.presheaf.stalk x) ∧
      IsClosed ({z} : Set (pullback p (X.fromSpecStalk x) : Scheme.{u})) := by
  let s := X.fromSpecStalk x
  let a := pullback.fst p s
  obtain ⟨z, hz, hqz⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := s) y
    (IsLocalRing.closedPoint (X.presheaf.stalk x))
    (hpx.trans (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)).symm)
  refine ⟨z, hz, hqz, ?_⟩
  have he : a ⁻¹' ({y} : Set Y) = {z} := by
    ext w
    change a w = y ↔ w = z
    rw [← hz]
    exact a.isEmbedding.injective.eq_iff
  exact he ▸ hy.preimage a.continuous

end AlgebraicGeometry.Scheme
