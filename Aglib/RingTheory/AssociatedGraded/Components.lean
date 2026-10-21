/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # The actual ideal-power quotients as homogeneous components -/

@[expose] public noncomputable section

open Polynomial
universe u
namespace Ideal
variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The original homogeneous monomial, as a linear map from its coefficient ideal. -/
def reesHomogeneousLinearMap (n : ℕ) : ↥(I ^ n : Ideal A) →ₗ[A] reesAlgebra I where
  toFun a := reesAlgebra.homogeneous I n a
  map_add' a b := by
    apply Subtype.ext
    exact map_add (monomial n) (a : A) (b : A)
  map_smul' r a := by
    apply Subtype.ext
    exact (monomial n).map_smul r (a : A)

/-- Map an ideal-power coefficient into its actual homogeneous quotient component. -/
def associatedGradedComponentMap (n : ℕ) :
    ↥(I ^ n : Ideal A) →ₗ[A] I.associatedGradedGrading n :=
  (((Ideal.Quotient.mkₐ A I.associatedGradedIdeal).toLinearMap).comp
    (I.reesHomogeneousLinearMap n)).codRestrict (I.associatedGradedGrading n)
    (fun a => Submodule.mem_map.mpr
      ⟨reesAlgebra.homogeneous I n a, (reesAlgebra.homogeneous I n a).property, rfl⟩)

@[simp]
lemma associatedGradedComponentMap_coe (n : ℕ) (a : ↥(I ^ n : Ideal A)) :
    (I.associatedGradedComponentMap n a : I.associatedGraded) =
      Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.homogeneous I n a) := rfl

lemma associatedGradedComponentMap_surjective (n : ℕ) :
    Function.Surjective (I.associatedGradedComponentMap n) := by
  intro x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.property
  refine ⟨⟨(p : A[X]).coeff n, p.property n⟩, ?_⟩
  apply Subtype.ext
  rw [I.associatedGradedComponentMap_coe]
  have he : (reesAlgebra.homogeneous I n
      ⟨(p : A[X]).coeff n, p.property n⟩ : reesAlgebra I) = p := by
    apply Subtype.ext
    exact (reesAlgebra.eq_monomial_coeff hp).symm
  simpa only [he, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] using hpx

lemma associatedGradedComponentMap_eq_zero_iff (n : ℕ) (a : ↥(I ^ n : Ideal A)) :
    I.associatedGradedComponentMap n a = 0 ↔ (a : A) ∈ I ^ (n + 1) := by
  rw [← Subtype.val_inj, I.associatedGradedComponentMap_coe,
    ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem, I.mem_associatedGradedIdeal_iff]
  constructor
  · intro h
    simpa [reesAlgebra.homogeneous] using h n
  · intro h m
    by_cases hm : n = m
    · subst m; simpa [reesAlgebra.homogeneous] using h
    · simp [reesAlgebra.homogeneous, coeff_monomial, hm]

/-- The next ideal power as a submodule of the preceding ideal power. -/
def associatedGradedComponentRelations (n : ℕ) : Submodule A ↥(I ^ n : Ideal A) :=
  Submodule.comap (I ^ n : Ideal A).subtype (I ^ (n + 1) : Ideal A)

lemma ker_associatedGradedComponentMap (n : ℕ) :
    LinearMap.ker (I.associatedGradedComponentMap n) =
      I.associatedGradedComponentRelations n := by
  ext a
  exact I.associatedGradedComponentMap_eq_zero_iff n a

/-- The degree-n component is canonically the quotient of consecutive ideal powers. -/
def associatedGradedComponentEquiv (n : ℕ) :
    (↥(I ^ n : Ideal A) ⧸ I.associatedGradedComponentRelations n) ≃ₗ[A]
      I.associatedGradedGrading n :=
  (Submodule.quotEquivOfEq _ _ (I.ker_associatedGradedComponentMap n).symm).trans
    (LinearMap.quotKerEquivOfSurjective (I.associatedGradedComponentMap n)
      (I.associatedGradedComponentMap_surjective n))

@[simp]
lemma associatedGradedComponentEquiv_mk (n : ℕ) (a : ↥(I ^ n : Ideal A)) :
    I.associatedGradedComponentEquiv n (Submodule.Quotient.mk a) =
      I.associatedGradedComponentMap n a := rfl

end Ideal
