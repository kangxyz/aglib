/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Original affine fibre points under a Galois ring action -/

@[expose] public noncomputable section

open CategoryTheory
open scoped Pointwise

namespace AlgebraicGeometry.Spec

universe u

variable (R B G : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G R B]

include G

/-- Prime transitivity as an actual spectrum automorphism over the original base.
The inverse ring automorphism accounts for the contravariance of spectrum. -/
theorem exists_iso_over_eq_of_image_eq (x y : Spec (.of B))
    (h : Spec.algebraMap R B x = Spec.algebraMap R B y) :
    ∃ e : Spec (.of B) ≅ Spec (.of B),
      e.hom ≫ Spec.algebraMap R B = Spec.algebraMap R B ∧ e.hom x = y := by
  let p : Ideal R := x.asIdeal.under R
  have : x.asIdeal.IsPrime := x.isPrime
  have : y.asIdeal.IsPrime := y.isPrime
  have : x.asIdeal.LiesOver p := ⟨rfl⟩
  have : y.asIdeal.LiesOver p := ⟨by
    exact congrArg PrimeSpectrum.asIdeal h⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p x.asIdeal y.asIdeal G
  let a := (MulSemiringAction.toAlgEquiv R B σ).symm
  let e := Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.op
  refine ⟨e, ?_, ?_⟩
  · exact Spec.map_algHom_algebraMap a.toAlgHom
  · apply PrimeSpectrum.ext
    change x.asIdeal.comap a.toRingHom = y.asIdeal
    rw [← hσ, Ideal.pointwise_smul_eq_comap]
    rfl

/-- Transfer the same orbit statement through a supplied original affine chart. -/
theorem exists_iso_over_eq_of_affine_image_eq {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) (c : Spec (.of B) ≅ Z)
    (hc : c.hom ≫ f = Spec.algebraMap R B) (x y : Z) (h : f x = f y) :
    ∃ e : Z ≅ Z, e.hom ≫ f = f ∧ e.hom x = y := by
  have hci : c.inv ≫ Spec.algebraMap R B = f := by rw [← hc]; simp
  have hxy : Spec.algebraMap R B (c.inv x) =
      Spec.algebraMap R B (c.inv y) := by
    simpa only [← Scheme.Hom.comp_apply, hci] using h
  obtain ⟨e, he, hp⟩ := exists_iso_over_eq_of_image_eq R B G (c.inv x) (c.inv y) hxy
  refine ⟨c.symm ≪≫ e ≪≫ c, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hc, he, hci]
  · change c.hom (e.hom (c.inv x)) = y
    rw [hp]
    change (c.inv ≫ c.hom) y = y
    rw [Iso.inv_hom_id]
    rfl

end AlgebraicGeometry.Spec
