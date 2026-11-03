/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# A residue-transcendental element as an actual local fraction

The original birational function-field map expresses a selected stalk element
as a fraction of elements of the original target stalk. Transcendence of its
original residue forces both numerator and denominator into the original
maximal ideal. Both the stalk equation and residue scalar map are retained.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- A selected residue-transcendental element is a unit and has an actual
fraction presentation with nonzero numerator and denominator in the original
target maximal ideal. The displayed equation uses exactly `p.stalkMap z`. -/
theorem exists_local_fraction_of_transcendental_residue
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Y) [IsDominant p]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap p)))
    (z : X) (u : X.presheaf.stalk z)
    (htrans : letI := (p.residueFieldMap z).hom.toAlgebra
      Transcendental (Y.residueField (p z)) (X.residue z u)) :
    IsUnit u ∧ ∃ a b : Y.presheaf.stalk (p z),
      a ≠ 0 ∧ b ≠ 0 ∧
      a ∈ IsLocalRing.maximalIdeal _ ∧ b ∈ IsLocalRing.maximalIdeal _ ∧
      u * p.stalkMap z b = p.stalkMap z a := by
  let R := Y.presheaf.stalk (p z)
  let D := X.presheaf.stalk z
  let φ : R →+* D := (p.stalkMap z).hom
  let : Algebra (Y.residueField (p z)) (X.residueField z) :=
    (p.residueFieldMap z).hom.toAlgebra
  have hres0 : X.residue z u ≠ 0 := by
    intro hz
    apply htrans
    rw [hz]
    exact isAlgebraic_zero
  have hu : IsUnit u := (IsLocalRing.residue_ne_zero_iff_isUnit u).mp hres0
  have hu0 : u ≠ 0 := hu.ne_zero
  let := hff
  obtain ⟨v, hv⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (functionFieldMap p))).2 (algebraMap D X.functionField u)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R v
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbF : functionFieldMap p (algebraMap R Y.functionField b) ≠ 0 := by
    apply (map_ne_zero (functionFieldMap p)).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective R Y.functionField)).mpr hb0
  have hφbF : algebraMap D X.functionField (φ b) ≠ 0 := by
    rw [← functionFieldMap_stalk p z]
    exact hbF
  have hφb : φ b ≠ 0 := fun hz ↦ hφbF (by rw [hz, map_zero])
  have hfrac : algebraMap D X.functionField (φ a) /
      algebraMap D X.functionField (φ b) = algebraMap D X.functionField u := by
    rw [← functionFieldMap_stalk p z, ← functionFieldMap_stalk p z, ← map_div₀, hab]
    exact hv
  have hcross : u * φ b = φ a := by
    apply IsFractionRing.injective D X.functionField
    rw [map_mul]
    exact ((div_eq_iff hφbF).mp hfrac).symm
  have hnB : ¬ IsUnit b := by
    intro hbunit
    let v := hbunit.unit
    have hvb : (v : R) = b := hbunit.unit_spec
    let t : R := a * (↑v⁻¹ : R)
    have htb : t * b = a := by
      rw [← hvb]
      simp [t, mul_assoc]
    have hut : u = φ t := by
      apply mul_right_cancel₀ hφb
      calc
        u * φ b = φ a := hcross
        _ = φ (t * b) := congrArg φ htb.symm
        _ = φ t * φ b := map_mul φ t b
    have hres : X.residue z u = (p.residueFieldMap z) (Y.residue (p z) t) := by
      rw [hut]
      exact (congrArg (fun k : R ⟶ X.residueField z ↦ k t) (residue_residueFieldMap p z)).symm
    apply htrans
    rw [hres]
    exact isAlgebraic_algebraMap (R := Y.residueField (p z))
      (A := X.residueField z) (Y.residue (p z) t)
  have hnA : ¬ IsUnit a := by
    intro haunit
    have hprod : IsUnit (u * φ b) := hcross.symm ▸ haunit.map φ
    exact hnB (isUnit_of_map_unit φ b (isUnit_of_mul_isUnit_right hprod))
  have ha0 : a ≠ 0 := by
    intro hz
    have hzero : u * φ b = 0 := by simpa only [hz, map_zero] using hcross
    exact (mul_ne_zero hu0 hφb) hzero
  exact ⟨hu, a, b, ha0, hb0, hnA, hnB, hcross⟩

end AlgebraicGeometry.Scheme.NormalizedPointDomination
