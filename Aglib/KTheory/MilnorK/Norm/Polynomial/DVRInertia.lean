/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRTrace
public import Aglib.RingTheory.DVRRamificationDegree
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Actual residue automorphisms of a finite local Galois extension

The residue homomorphism is induced by `galRestrict`, not by a chosen action.
Its surjectivity comes from the native stabilizer-to-residue-automorphism theorem.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing

variable {F : Type*} [Field F] [CharZero F]

local instance (p : MonicIrreducible F) : Module.Finite F (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R F] [IsFractionRing R F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Algebra S (AdjoinRoot p.val)]
  [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  [IsLocalHom (algebraMap R S)]

/-- The actual automorphism induced on the residue extension. -/
def residueGaloisHom : Gal(AdjoinRoot p.val/F) →*
    Gal((ResidueField S)/(ResidueField R)) where
  toFun σ := ResidueField.mapAlgEquiv' (galRestrict R F (AdjoinRoot p.val) S σ)
  map_one' := by
    ext x
    obtain ⟨s, rfl⟩ := residue_surjective x
    simp only [ResidueField.mapAlgEquiv'_residue, map_one, AlgEquiv.one_apply]
  map_mul' σ τ := by
    ext x
    obtain ⟨s, rfl⟩ := residue_surjective x
    simp only [ResidueField.mapAlgEquiv'_residue, AlgEquiv.mul_apply, map_mul]

omit [IsFractionRing S (AdjoinRoot p.val)] in
/-- This homomorphism has exactly the quotient map used in the tame trace identity. -/
theorem residueGaloisHom_toRingHom (σ : Gal(AdjoinRoot p.val/F)) :
    (residueGaloisHom R p S σ).toRingHom =
      (ResidueField.mapEquiv
        (galRestrict R F (AdjoinRoot p.val) S σ).toRingEquiv).toRingHom := rfl

/-- Every residue automorphism is induced by an actual field automorphism. -/
theorem residueGaloisHom_surjective [Normal F (AdjoinRoot p.val)] :
    Function.Surjective (residueGaloisHom R p S) := by
  let := IsIntegralClosure.MulSemiringAction R F (AdjoinRoot p.val) S
  have : IsGalois F (AdjoinRoot p.val) := {}
  have : Algebra.IsIntegral R S := ⟨IsIntegralClosure.isIntegral R (AdjoinRoot p.val)⟩
  have : IsGaloisGroup Gal(AdjoinRoot p.val/F) R S :=
    IsGaloisGroup.of_isFractionRing _ _ _ F (AdjoinRoot p.val)
  intro τ
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective
    Gal(AdjoinRoot p.val/F) (maximalIdeal R) (maximalIdeal S) τ
  refine ⟨σ.val, ?_⟩
  apply AlgEquiv.ext
  intro x
  obtain ⟨s, rfl⟩ := residue_surjective x
  exact DFunLike.congr_fun hσ (IsLocalRing.residue S s)

/-- The actual residue extension of a finite normal local extension is normal. -/
theorem residueField_normal [Normal F (AdjoinRoot p.val)] :
    Normal (ResidueField R) (ResidueField S) := by
  let := IsIntegralClosure.MulSemiringAction R F (AdjoinRoot p.val) S
  have : IsGalois F (AdjoinRoot p.val) := {}
  have : Algebra.IsIntegral R S := ⟨IsIntegralClosure.isIntegral R (AdjoinRoot p.val)⟩
  have : IsGaloisGroup Gal(AdjoinRoot p.val/F) R S :=
    IsGaloisGroup.of_isFractionRing _ _ _ F (AdjoinRoot p.val)
  exact Ideal.Quotient.normal Gal(AdjoinRoot p.val/F) (maximalIdeal R) (maximalIdeal S)

variable [Normal F (AdjoinRoot p.val)] [Module.Finite R S]
  [Module.IsTorsionFree R S] [CharZero (ResidueField R)]

/-- The kernel has the literal ramification exponent from the uniformizer equation. -/
theorem residueGaloisHom_card_ker
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    Nat.card (residueGaloisHom R p S).ker = e := by
  have : IsGalois F (AdjoinRoot p.val) := {}
  have : Normal (ResidueField R) (ResidueField S) := residueField_normal R p S
  have : IsGalois (ResidueField R) (ResidueField S) := {}
  have hindex : (residueGaloisHom R p S).ker.index =
      Module.finrank (ResidueField R) (ResidueField S) := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        (residueGaloisHom R p S) (residueGaloisHom_surjective R p S)).toEquiv,
      IsGalois.card_aut_eq_finrank]
  have hcard := (residueGaloisHom R p S).ker.card_mul_index
  rw [hindex, IsGalois.card_aut_eq_finrank,
    IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
      R S F (AdjoinRoot p.val) hπ hϖ u e he] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Module.finrank_pos :
    0 < Module.finrank (ResidueField R) (ResidueField S)) hcard

/-- Every actual residue automorphism has exactly `e` lifts to field automorphisms. -/
theorem residueGaloisHom_card_fiber
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (τ : Gal((ResidueField S)/(ResidueField R))) :
    Nat.card {σ : Gal(AdjoinRoot p.val/F) // residueGaloisHom R p S σ = τ} = e := by
  have h := Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective
    (residueGaloisHom_surjective R p S) τ)
  exact h.trans (residueGaloisHom_card_ker R p S hπ hϖ u e he)

end MilnorK.PolynomialNorm
