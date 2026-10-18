/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.HenselianPrincipalRoots
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Principal-unit normalization of an actual uniformizer equation

A surjective actual residue map lets one lift the residue of an extension unit
to a base unit. Hensel lifting then removes the remaining principal unit by a
root with residue exactly one, when the exponent is invertible. Applied to a
literal uniformizer equation, this produces a unit multiple of the original
uniformizer whose power is a base element up to a base unit.

No field degree, monogenic integral basis, norm identity or cancellation of
powers of residues is assumed. The degree-one residue-field corollary derives
surjectivity from the actual coefficient algebra map.
-/

@[expose] public noncomputable section

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [IsLocalRing R]
  [CommRing S] [IsLocalRing S] (j : R →+* S) [IsLocalHom j]

/-- A surjective residue map lifts the residue of an actual extension unit to
an actual base unit; no section of the residue field is assumed. -/
theorem exists_unit_residue_lift
    (hj : Function.Surjective (ResidueField.map j)) (u : Sˣ) :
    ∃ a : Rˣ, residue S (j (a : R)) = residue S (u : S) := by
  obtain ⟨c, hc⟩ := hj (residue S (u : S))
  obtain ⟨a, ha⟩ := residue_surjective c
  have hres : residue S (j a) = residue S (u : S) := by
    rw [← ResidueField.map_residue, ha, hc]
  have ha0 : residue R a ≠ 0 := by
    intro hz
    have hu : residue S (u : S) = 0 := by
      rw [← hres, ← ResidueField.map_residue, hz, map_zero]
    exact ((residue_ne_zero_iff_isUnit (u : S)).mpr u.isUnit) hu
  obtain ⟨a, rfl⟩ := (residue_ne_zero_iff_isUnit a).mp ha0
  exact ⟨a, hres⟩

end IsLocalRing

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [IsLocalRing R]
  [CommRing S] [HenselianLocalRing S] (j : R →+* S) [IsLocalHom j]

/-- Every extension unit is a base unit times an exponent-th power of an
actual principal unit. The root is explicitly required to have residue one. -/
theorem exists_base_unit_mul_principal_pow
    (hj : Function.Surjective (ResidueField.map j))
    (e : ℕ) (he : 0 < e) (heunit : IsUnit (e : S)) (u : Sˣ) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Units.map j.toMonoidHom a * v ^ e = u := by
  obtain ⟨a, ha⟩ := exists_unit_residue_lift j hj u
  let w : Sˣ := u * (Units.map j.toMonoidHom a)⁻¹
  have hw : residue S (w : S) = 1 := by
    change residue S ((u : S) * ((Units.map j.toMonoidHom a)⁻¹ : Sˣ)) = 1
    rw [map_mul, ← ha]
    exact (Units.map (residue S).toMonoidHom (Units.map j.toMonoidHom a)).val_inv
  obtain ⟨v, hv, hvpow⟩ :=
    HenselianLocalRing.PrincipalRoots.exists_pow_eq e he heunit w hw
  refine ⟨a, v, hv, ?_⟩
  rw [hvpow]
  dsimp only [w]
  rw [mul_left_comm, mul_inv_cancel, mul_one]

/-- The adjusted uniformizer remains irreducible and has residue-one ratio to
the old one. Its exponent power differs from the base uniformizer only by an
actual base unit. -/
theorem exists_principal_adjusted_uniformizer
    (hj : Function.Surjective (ResidueField.map j))
    {π : R} {ϖ : S} (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : 0 < e) (heunit : IsUnit (e : S))
    (hπ : j π = (u : S) * ϖ ^ e) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧
      j π = j (a : R) * ((v : S) * ϖ) ^ e := by
  obtain ⟨a, v, hv, huv⟩ := exists_base_unit_mul_principal_pow j hj e he heunit u
  refine ⟨a, v, hv, ?_, ?_⟩
  · simpa only [mul_comm] using (irreducible_mul_units v).mpr hϖ
  · rw [hπ, ← huv, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, mul_pow]
    change j (a : R) * (v : S) ^ e * ϖ ^ e = j (a : R) * ((v : S) ^ e * ϖ ^ e)
    exact mul_assoc _ _ _

end IsLocalRing

namespace HenselianLocalRing

variable (R S : Type*) [CommRing R] [IsLocalRing R]
  [CommRing S] [HenselianLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- Actual residue degree one supplies the needed residue-map surjectivity.
No assertion that arbitrary finite residue extensions are simple is used. -/
theorem exists_principal_adjusted_uniformizer_of_residue_finrank_one
    (hf : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) = 1)
    {π : R} {ϖ : S} (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : 0 < e) (heunit : IsUnit (e : S))
    (hπ : algebraMap R S π = (u : S) * ϖ ^ e) :
    ∃ (a : Rˣ) (v : Sˣ), IsLocalRing.residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧
      algebraMap R S π = algebraMap R S (a : R) * ((v : S) * ϖ) ^ e := by
  have hj : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S)) := by
    have hmap : IsLocalRing.ResidueField.map (algebraMap R S) =
        algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
      ext a
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
      rfl
    rw [hmap]
    exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hf).surjective
  exact IsLocalRing.exists_principal_adjusted_uniformizer (algebraMap R S) hj hϖ u e he heunit hπ

end HenselianLocalRing
