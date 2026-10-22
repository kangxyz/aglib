/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.FrobeniusCriterion
public import Aglib.FieldTheory.SeparablyGenerated.GeometricallyReduced

/-!
# Geometric reducedness under an actual scalar field equivalence
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Algebra

/-- Finite independence is unchanged by a specified isomorphism of scalar
fields, provided the actual scalar actions commute with that isomorphism. -/
theorem linearIndependent_iff_of_baseRingEquiv
    {S F L ι : Type*} [Field S] [Field F] [Field L]
    [Algebra S L] [Algebra F L] [Finite ι]
    (e : S ≃+* F) (hmap : ∀ s, algebraMap S L s = algebraMap F L (e s))
    (v : ι → L) : LinearIndependent S v ↔ LinearIndependent F v := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro hv
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hrel : ∑ i, e.symm (c i) • v i = 0 := by
      simpa only [Algebra.smul_def, hmap, RingEquiv.apply_symm_apply] using hc
    have hz := Fintype.linearIndependent_iff.mp hv (fun i => e.symm (c i)) hrel
    intro i
    apply e.symm.injective
    simpa only [map_zero] using hz i
  · intro hv
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hrel : ∑ i, e (c i) • v i = 0 := by
      simpa only [Algebra.smul_def, hmap] using hc
    have hz := Fintype.linearIndependent_iff.mp hv (fun i => e (c i)) hrel
    intro i
    apply e.injective
    simpa only [map_zero] using hz i

/-- Geometric reducedness descends through a specified isomorphism of the
base fields and its actual scalar square. This positive-characteristic proof
uses only finite power independence, not an abstract replacement of actions. -/
theorem isGeometricallyReduced_of_baseRingEquiv
    {S F L : Type*} [Field S] [Field F] [Field L]
    [Algebra S L] [Algebra F L]
    (p : ℕ) (hp : p.Prime) [ExpChar S p] [ExpChar F p]
    (e : S ≃+* F) (hmap : ∀ s, algebraMap S L s = algebraMap F L (e s))
    (h : IsGeometricallyReduced F L) : IsGeometricallyReduced S L := by
  let := h
  apply isGeometricallyReduced_of_linearIndependent_pow p hp
  intro n v hv
  apply (linearIndependent_iff_of_baseRingEquiv e hmap (fun i => v i ^ p)).mpr
  exact linearIndependent_pow_of_geometricallyReduced p hp
    ((linearIndependent_iff_of_baseRingEquiv e hmap v).mp hv)

end Algebra
