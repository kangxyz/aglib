/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Actual affine target charts and restricted original marks

A geometric point has an actual affine open spectrum neighborhood. Original
source and etale-chart marks lift to its literal pullbacks by their original
whole-map equations. No global section is required to land in this open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A field-valued point factors through an open immersion as soon as its
unique underlying point lies in the open. The field itself is unchanged. -/
theorem exists_fieldPoint_lift_of_mem_range
    {X O : Scheme.{u}} (j : O ⟶ X) [IsOpenImmersion j]
    (Ω : Type u) [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (hx : x (IsLocalRing.closedPoint Ω) ∈ Set.range j) :
    ∃ y : Spec (.of Ω) ⟶ O, y ≫ j = x := by
  have hrange : Set.range x ⊆ Set.range j := by
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    exact hx
  exact ⟨IsOpenImmersion.lift j x hrange, IsOpenImmersion.lift_fac j x hrange⟩

/-- Choose an actual affine open spectrum chart containing the whole given
field-valued point, and retain its original morphism by an exact triangle. -/
theorem exists_affineSpec_chart_of_fieldPoint
    {X : Scheme.{u}} (Ω : Type u) [Field Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra R Ω)
      (j : Spec (.of R) ⟶ X),
      IsOpenImmersion j ∧ Spec.algebraMap R Ω ≫ j = x := by
  obtain ⟨O, hO, hxO, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  let : IsAffine O.toScheme := hO
  have hrange : Set.range x ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    exact hxO
  let xO : Spec (.of Ω) ⟶ O.toScheme := IsOpenImmersion.lift O.ι x hrange
  have hx : xO ≫ O.ι = x := IsOpenImmersion.lift_fac O.ι x hrange
  let R : Type u := Γ(O.toScheme, ⊤)
  let : CommRing R := inferInstanceAs (CommRing Γ(O.toScheme, ⊤))
  let j : Spec (.of R) ⟶ X := O.toScheme.isoSpec.inv ≫ O.ι
  let y : Spec (.of Ω) ⟶ Spec (.of R) := xO ≫ O.toScheme.isoSpec.hom
  let alg : Algebra R Ω := (Spec.preimage y).hom.toAlgebra
  let : Algebra R Ω := alg
  have hy : Spec.algebraMap R Ω = y := Spec.map_preimage y
  have hj : y ≫ j = x := by
    simpa only [y, j, Category.assoc, Iso.hom_inv_id_assoc] using hx
  exact ⟨R, inferInstance, alg, j, inferInstance,
    (congrArg (fun f : Spec (.of Ω) ⟶ Spec (.of R) => f ≫ j) hy).trans hj⟩

namespace Etale

variable {X S O T : Scheme.{u}} (f : S ⟶ X) (j : O ⟶ X) (U : S.Etale)

/-- The actual etale chart after restricting its target by the given map. -/
abbrev targetRestriction : (pullback f j).Etale :=
  Scheme.Etale.mk (pullback.snd U.hom (pullback.fst f j))

/-- An original chart mark lifts to the actual target-restricted chart.
Only the mark itself, not a global section, must lie over the given target map. -/
def targetRestrictionPoint
    (m : T ⟶ U.left) (y : T ⟶ O) (h : m ≫ U.hom ≫ f = y ≫ j) :
    T ⟶ pullback U.hom (pullback.fst f j) :=
  pullback.lift m
    (pullback.lift (m ≫ U.hom) y ((Category.assoc m U.hom f).trans h))
    (by simp only [pullback.lift_fst])

@[reassoc (attr := simp)]
theorem targetRestrictionPoint_original
    (m : T ⟶ U.left) (y : T ⟶ O) (h : m ≫ U.hom ≫ f = y ≫ j) :
    targetRestrictionPoint f j U m y h ≫ pullback.fst U.hom (pullback.fst f j) = m :=
  pullback.lift_fst ..

@[simp, reassoc]
theorem targetRestrictionPoint_source
    (m : T ⟶ U.left) (y : T ⟶ O) (h : m ≫ U.hom ≫ f = y ≫ j) :
    targetRestrictionPoint f j U m y h ≫ (targetRestriction f j U).hom =
      pullback.lift (m ≫ U.hom) y ((Category.assoc m U.hom f).trans h) :=
  pullback.lift_snd ..

@[reassoc (attr := simp)]
theorem targetRestrictionPoint_target
    (m : T ⟶ U.left) (y : T ⟶ O) (h : m ≫ U.hom ≫ f = y ≫ j) :
    targetRestrictionPoint f j U m y h ≫ (targetRestriction f j U).hom ≫
      pullback.snd f j = y := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ pullback.snd f j)
      (targetRestrictionPoint_source f j U m y h)).trans (pullback.lift_snd ..))

/-- Every original field-valued chart mark above a point of the target open
has an actual restricted chart mark, even when no global section lands there. -/
theorem exists_targetRestrictionPoint_of_mem_range
    [IsOpenImmersion j] (Ω : Type u) [Field Ω] (m : Spec (.of Ω) ⟶ U.left)
    (hm : (m ≫ U.hom ≫ f) (IsLocalRing.closedPoint Ω) ∈ Set.range j) :
    ∃ (y : Spec (.of Ω) ⟶ O)
      (z : Spec (.of Ω) ⟶ pullback U.hom (pullback.fst f j)),
      y ≫ j = m ≫ U.hom ≫ f ∧
      z ≫ pullback.fst U.hom (pullback.fst f j) = m ∧
      z ≫ (targetRestriction f j U).hom ≫ pullback.snd f j = y := by
  obtain ⟨y, hy⟩ := exists_fieldPoint_lift_of_mem_range j Ω (m ≫ U.hom ≫ f) hm
  exact ⟨y, targetRestrictionPoint f j U m y hy.symm, hy,
    targetRestrictionPoint_original f j U m y hy.symm,
    targetRestrictionPoint_target f j U m y hy.symm⟩

end Etale

end AlgebraicGeometry.Scheme
