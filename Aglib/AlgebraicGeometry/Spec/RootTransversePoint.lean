/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.RootTransverseSection
public import Aglib.RingTheory.Kummer.TransversePoint

/-! # Actual transverse points of the original root chart

A whole map from the actual local ring into a root chart is stronger than a
fraction-field section. Its image of the root already lies in that ring, so an
irreducible parameter forces exponent one without choosing a fraction field.
-/

@[expose] public noncomputable section

open CategoryTheory Algebra.Kummer Polynomial

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]

/-- A whole transverse point forces exponent one and etaleness of the original
chart map. No field, normality or positivity premise is necessary. -/
theorem exponent_eq_one_and_etale_of_transversePoint
    (n : ℕ) (f : A) (hf : Irreducible (algebraMap A D f))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of A))
    (c : Spec (.of (RootAlgebra n f)) ≅ Z)
    (hc : c.hom ≫ p = Spec.algebraMap A (RootAlgebra n f))
    (s : Spec (.of D) ⟶ Z) (hs : s ≫ p = Spec.algebraMap A D) :
    n = 1 ∧ Etale p := by
  have hci : c.inv ≫ Spec.algebraMap A (RootAlgebra n f) = p := by
    rw [← hc, Iso.inv_hom_id_assoc]
  obtain ⟨t, _⟩ := exists_rootAlgHom_of_specPoint A D n f (s ≫ c.inv) (by
    rw [Category.assoc, hci, hs])
  have hn := Algebra.Kummer.exponent_eq_one_of_transversePoint n f hf t
  let : Algebra.Etale A (RootAlgebra n f) := Algebra.Kummer.etale_of_transversePoint n f hf t
  let : Etale (Spec.algebraMap A (RootAlgebra n f)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  refine ⟨hn, ?_⟩
  rw [← hci]
  infer_instance

end AlgebraicGeometry.Scheme.Kummer
