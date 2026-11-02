/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OpenRestriction

/-!
# The Picard group of an open subscheme of a curve

The examples restate, for a smooth proper geometrically connected curve over an algebraically
closed field and an open immersion `j : U ⟶ X`, that `Pic(X) → Pic(U)` is surjective, and that
when the image of `j` misses a closed point (for instance `U = X − D` with `D` a nonempty set of
closed points) already the degree-zero classes surject. They also check the geometric
properties of `U` used in the proof and guard the axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AglibTest.CurvePicardOpenRestriction

variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]

/-- The open subscheme is Noetherian, of dimension at most one, smooth of relative dimension one
over `k`, and its closed points have discrete valuation rings. -/
example [IsIntegral U] (y : Scheme.ClosedPoint U) :
    IsNoetherian U ∧ topologicalKrullDim U ≤ 1 ∧ SmoothOfRelativeDimension 1 (j ≫ X.hom) ∧
      IsDiscreteValuationRing (U.presheaf.stalk y.val) :=
  ⟨Curve.isNoetherian_of_isOpenImmersion hX j,
    Curve.topologicalKrullDim_le_one_of_isOpenImmersion hX j,
    Curve.smoothOfRelativeDimension_one_of_isOpenImmersion hX j,
    Curve.isDiscreteValuationRing_stalk_of_isOpenImmersion hX j y⟩

variable [IsAlgClosed k]

/-- `Pic(X) → Pic(U)` is surjective. -/
example : Function.Surjective (pullbackClass j) :=
  Curve.pullbackClass_surjective_of_isOpenImmersion hX j

/-- For a nonempty closed complement, degree-zero Picard classes already surject. -/
example (D : Set X.left) (hDne : D.Nonempty) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
    (hD : Set.range j = Dᶜ) (c : PicardGroup U) :
    ∃ b : PicardGroup X.left,
      Curve.curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension
        Curve.Picard.Degree.properCurveProductFormula X hX b = 0 ∧ pullbackClass j b = c := by
  obtain ⟨x, hxD⟩ := hDne
  have hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j :=
    ⟨x, hclosed x hxD, by rw [hD]; exact fun h => h hxD⟩
  exact Curve.exists_curveDegree_eq_zero_pullbackClass_eq_of_isOpenImmersion hX j hx c

end AglibTest.CurvePicardOpenRestriction

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.isNoetherian_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isNoetherian_of_isOpenImmersion

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.smoothOfRelativeDimension_one_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.smoothOfRelativeDimension_one_of_isOpenImmersion

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.topologicalKrullDim_le_one_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.topologicalKrullDim_le_one_of_isOpenImmersion

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.isDiscreteValuationRing_stalk_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isDiscreteValuationRing_stalk_of_isOpenImmersion

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_curveDegree_eq_zero_pullbackClass_eq_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_curveDegree_eq_zero_pullbackClass_eq_of_isOpenImmersion

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.pullbackClass_surjective_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.pullbackClass_surjective_of_isOpenImmersion
