/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.TransverseSection
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Transverse generic sections of original scheme root charts

Spec fullness transports the actual generic section through the supplied
original chart. The original root equation forces exponent one, and etaleness
is transported back to the unchanged structural morphism. No field embedding
or algebraic section is an additional premise.
-/

@[expose] public noncomputable section

open CategoryTheory Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (A D K : Type u) [CommRing A] [CommRing D] [CommRing K]
  [Algebra A D] [Algebra D K] [Algebra A K] [IsScalarTower A D K]

/-- An original affine root point supplies the actual scalar-compatible root
algebra map, retaining its whole spectrum map. -/
theorem exists_rootAlgHom_of_specPoint (n : ℕ) (f : A)
    (s : Spec (.of K) ⟶ Spec (.of (RootAlgebra n f)))
    (hs : s ≫ Spec.algebraMap A (RootAlgebra n f) = Spec.algebraMap A K) :
    ∃ t : RootAlgebra n f →ₐ[A] K,
      Spec.map (CommRingCat.ofHom t.toRingHom) = s := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective s
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap A (RootAlgebra n f)) ≫ φ) =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) := by
    rw [Spec.map_comp, hφ]
    exact hs
  have hc := Spec.map_injective hmap
  refine ⟨{ φ.hom with commutes' := ?_ }, hφ⟩
  intro a
  exact congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of K => q a) hc

/-- A genuine transverse generic section forces the original chart exponent
to be one and makes its unchanged structural morphism etale. -/
theorem exponent_eq_one_and_etale_of_transverseSection
    [IsIntegrallyClosed D] [IsFractionRing D K]
    (n : ℕ) (f : A) (hf : Irreducible (algebraMap A D f))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of A))
    (c : Spec (.of (RootAlgebra n f)) ≅ Z)
    (hc : c.hom ≫ p = Spec.algebraMap A (RootAlgebra n f))
    (s : Spec (.of K) ⟶ Z) (hs : s ≫ p = Spec.algebraMap A K) :
    n = 1 ∧ Etale p := by
  have hci : c.inv ≫ Spec.algebraMap A (RootAlgebra n f) = p := by
    rw [← hc, Iso.inv_hom_id_assoc]
  obtain ⟨t, _⟩ := exists_rootAlgHom_of_specPoint A K n f (s ≫ c.inv) (by
    rw [Category.assoc, hci, hs])
  have hn := Algebra.Kummer.exponent_eq_one_of_transverseSection (R := D) n f hf t
  let : Algebra.Etale A (RootAlgebra n f) :=
    Algebra.Kummer.etale_of_transverseSection (R := D) n f hf t
  let : Etale (Spec.algebraMap A (RootAlgebra n f)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  refine ⟨hn, ?_⟩
  rw [← hci]
  infer_instance

end AlgebraicGeometry.Scheme.Kummer
