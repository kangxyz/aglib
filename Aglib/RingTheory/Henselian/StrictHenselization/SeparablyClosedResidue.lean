/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Separably closed residue of the geometric neighborhood colimit

The chosen-field-valued map factors through the native residue field. If the
chosen field is separably closed, every monic irreducible separable residue
polynomial has a root: lift its coefficients, choose a simple root in the chosen
field, and use the actual standard-etale stage of the colimit. The chosen-field
map need not be surjective, and no equality with that field is asserted.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace GeometricEtaleColimit

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- The canonical embedding of the colimit's residue field into the chosen
point field. It is not generally surjective. -/
def residueFieldEmbedding : ResidueField (GeometricEtaleColimit R Ω) →+* Ω :=
  ResidueField.lift (residue R Ω).toRingHom

@[simp]
lemma residueFieldEmbedding_comp_residue :
    (residueFieldEmbedding R Ω).comp (IsLocalRing.residue (GeometricEtaleColimit R Ω)) =
      (residue R Ω).toRingHom :=
  ResidueField.lift_comp_residue _

/-- A separably closed chosen point field makes the actual neighborhood
colimit strictly local. -/
instance [IsSepClosed Ω] : IsSepClosed (ResidueField (GeometricEtaleColimit R Ω)) := by
  apply IsSepClosed.of_exists_root
  intro p hp hirr hsep
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue (GeometricEtaleColimit R Ω)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact IsLocalRing.residue_surjective (R := GeometricEtaleColimit R Ω) (p.coeff i)
  obtain ⟨q, hq, _, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  have hmap : q.map (residue R Ω).toRingHom = p.map (residueFieldEmbedding R Ω) := by
    rw [← hq, Polynomial.map_map, residueFieldEmbedding_comp_residue]
  obtain ⟨b, hb⟩ := IsSepClosed.exists_root (p.map (residueFieldEmbedding R Ω))
    (by rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne')
    hsep.map
  have hdb : (q.derivative.map (residue R Ω).toRingHom).eval b ≠ 0 := by
    rw [← Polynomial.derivative_map, hmap, Polynomial.derivative_map,
      Polynomial.eval_map]
    apply hsep.eval₂_derivative_ne_zero (residueFieldEmbedding R Ω)
    change (p.map (residueFieldEmbedding R Ω)).eval b = 0 at hb
    simpa only [Polynomial.eval_map] using hb
  obtain ⟨a, ha, _⟩ := exists_root_of_monic_residue R Ω q hqm b (by rwa [hmap]) hdb
  refine ⟨IsLocalRing.residue (GeometricEtaleColimit R Ω) a, ?_⟩
  rw [← hq, Polynomial.eval_map_apply]
  rw [show q.eval a = 0 from ha, map_zero]

end GeometricEtaleColimit
