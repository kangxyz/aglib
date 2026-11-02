/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.SelectedFraction

/-!
# Maximal-ideal membership of the retained transformed fraction

Unlike choosing a new fraction, this lemma retains the supplied numerator,
denominator and original stalk equation. It applies after simultaneous
exceptional division and finite residue-field extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- Every retained fraction equation for a residue-transcendental element
has its numerator and denominator in the actual target maximal ideal.
No birationality or domain hypothesis is needed for this local assertion. -/
theorem fraction_mem_maximalIdeal_of_transcendental_residue
    {X Y : Scheme.{u}} (p : X ⟶ Y) (z : X) (u : X.presheaf.stalk z)
    (a b : Y.presheaf.stalk (p z))
    (htrans : letI := (p.residueFieldMap z).hom.toAlgebra
      Transcendental (Y.residueField (p z)) (X.residue z u))
    (hcross : u * p.stalkMap z b = p.stalkMap z a) :
    a ∈ IsLocalRing.maximalIdeal _ ∧ b ∈ IsLocalRing.maximalIdeal _ := by
  let R := Y.presheaf.stalk (p z)
  let D := X.presheaf.stalk z
  let φ : R →+* D := (p.stalkMap z).hom
  let : Algebra (Y.residueField (p z)) (X.residueField z) :=
    (p.residueFieldMap z).hom.toAlgebra
  have hnB : ¬ IsUnit b := by
    intro hbunit
    let v := hbunit.unit
    have hvb : (v : R) = b := hbunit.unit_spec
    let t : R := a * (↑v⁻¹ : R)
    have htb : t * b = a := by
      rw [← hvb]
      simp [t, mul_assoc]
    have hut : u = φ t := by
      apply (hbunit.map φ).mul_right_cancel
      calc
        u * φ b = φ a := hcross
        _ = φ (t * b) := congrArg φ htb.symm
        _ = φ t * φ b := map_mul φ t b
    have hres : X.residue z u = (p.residueFieldMap z) (Y.residue (p z) t) := by
      rw [hut]
      exact (congrArg (fun k : R ⟶ X.residueField z ↦ k t)
        (residue_residueFieldMap p z)).symm
    apply htrans
    rw [hres]
    exact isAlgebraic_algebraMap (R := Y.residueField (p z))
      (A := X.residueField z) (Y.residue (p z) t)
  have hnA : ¬ IsUnit a := by
    intro haunit
    have hprod : IsUnit (u * φ b) := hcross.symm ▸ haunit.map φ
    exact hnB (isUnit_of_map_unit φ b (isUnit_of_mul_isUnit_right hprod))
  exact ⟨hnA, hnB⟩

end AlgebraicGeometry.Scheme.NormalizedPointDomination
