/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRInertia
public import Aglib.KTheory.MilnorK.RestrictionKernel

/-!
# Actual residue defects of polynomial-presentation norms

The transported Galois trace keeps the chosen polynomial presentation and all
literal field maps visible. Genuine residue fibers have the literal ramification
size, so ramification times the restricted norm-residue defect vanishes on every
class. The actual degree formula and an auxiliary residue-degree retraction then
show that the original polynomial degree kills the defect. No generator
independence, norm-residue square or norm tower is assumed. Normality, finite
integral closure and characteristic zero of the residue field remain explicit;
this is an annihilator theorem, not vanishing of the defect.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {F E : Type*} [Field F] [Field E] [CharZero F] [Algebra F E]

local instance (p : MonicIrreducible F) : Module.Finite F (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

open Classical in
/-- The split trace formula transported through a specified actual root-field
isomorphism. It does not replace the presentation norm by a canonical norm. -/
theorem polynomialNorm_restrict_eq_sum_galois_of_algEquiv
    [Module.Finite F E] [Normal F E] (n : ℕ) (p : MonicIrreducible F)
    (ε : AdjoinRoot p.val ≃ₐ[F] E) (x : K E n) :
    map n (algebraMap F E) (polynomialNorm n p (map n ε.symm.toRingHom x)) =
      ∑ σ : Gal(E/F), map n σ.toRingHom x := by
  classical
  let : Normal F (AdjoinRoot p.val) := Normal.of_algEquiv ε.symm
  have hc : ε.toRingHom.comp (algebraMap F (AdjoinRoot p.val)) = algebraMap F E := by
    ext a
    exact ε.commutes a
  calc
    _ = map n ε.toRingHom
        (map n (algebraMap F (AdjoinRoot p.val))
          (polynomialNorm n p (map n ε.symm.toRingHom x))) := by
      symm
      rw [← LinearMap.comp_apply, ← map_comp, hc]
    _ = ∑ σ : Gal(AdjoinRoot p.val/F),
        map n ε.toRingHom (map n σ.toRingHom (map n ε.symm.toRingHom x)) := by
      rw [polynomialNorm_restrict_eq_sum_galois, map_sum]
    _ = _ := by
      apply Fintype.sum_equiv (AlgEquiv.autCongr ε).toEquiv
      intro σ
      rw [← LinearMap.comp_apply, ← map_comp, ← LinearMap.comp_apply, ← map_comp]
      rfl

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R F] [IsFractionRing R F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Algebra S (AdjoinRoot p.val)]
  [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Normal F (AdjoinRoot p.val)] [CharZero (IsLocalRing.ResidueField R)]

open IsLocalRing

open Classical in
/-- Regrouping the actual field-automorphism trace by its genuine residue fibers
introduces exactly the literal ramification exponent. -/
theorem sum_residueGaloisHom_eq_ramification_smul (n : ℕ)
    (y : K (ResidueField S) n)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    (∑ σ : Gal(AdjoinRoot p.val/F), map n (residueGaloisHom R p S σ).toRingHom y) =
      (e : ℤ) • ∑ τ : Gal((ResidueField S)/(ResidueField R)), map n τ.toRingHom y := by
  classical
  rw [← Fintype.sum_fiberwise' (residueGaloisHom R p S)
    (fun τ => map n τ.toRingHom y), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  have hc : Fintype.card {σ // residueGaloisHom R p S σ = τ} = e := by
    rw [← Nat.card_eq_fintype_card]
    exact residueGaloisHom_card_fiber R p S hπ hϖ u e he τ
  simp only [Finset.sum_const, Finset.card_univ, hc, natCast_zsmul]

/-- The actual norm-residue defect becomes zero after residue restriction and
multiplication by the literal ramification exponent. This holds on all classes. -/
theorem ramification_smul_restrict_residue_polynomialNorm_defect (n : ℕ)
    (x : K (AdjoinRoot p.val) (n + 1))
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    (e : ℤ) • map n (algebraMap (ResidueField R) (ResidueField S))
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue S (AdjoinRoot p.val) n x))) = 0 := by
  classical
  let : Normal (ResidueField R) (ResidueField S) := residueField_normal R p S
  have hκ : algebraMap (ResidueField R) (ResidueField S) =
      ResidueField.map (algebraMap R S) := by
    ext a
    obtain ⟨r, rfl⟩ := residue_surjective a
    rfl
  rw [map_sub, smul_sub, sub_eq_zero]
  calc
    _ = ∑ σ : Gal(AdjoinRoot p.val/F),
        map n (residueGaloisHom R p S σ).toRingHom
          (DVR.residue S (AdjoinRoot p.val) n x) := by
      simpa only [residueGaloisHom_toRingHom, hκ] using
        residue_polynomialNorm_galois_trace R p S n x hπ hϖ u e he
    _ = (e : ℤ) • ∑ τ : Gal((ResidueField S)/(ResidueField R)),
        map n τ.toRingHom (DVR.residue S (AdjoinRoot p.val) n x) :=
      sum_residueGaloisHom_eq_ramification_smul R p S n _ hπ hϖ u e he
    _ = _ := by rw [polynomialNorm_restrict_eq_sum_galois_of_algEquiv]

/-- The degree of the original presentation annihilates its all-class tame
norm-residue defect. In prime degree this is the needed p-annihilator, not yet
vanishing of the defect or a completed norm-residue square. -/
theorem degree_smul_residue_polynomialNorm_defect (n : ℕ)
    (x : K (AdjoinRoot p.val) (n + 1))
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    (p.val.natDegree : ℤ) •
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue S (AdjoinRoot p.val) n x))) = 0 := by
  have hd := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F (AdjoinRoot p.val) hπ hϖ u e he
  rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim] at hd
  have h := mul_finrank_smul_eq_zero_of_smul_map_eq_zero
    (ResidueField R) (ResidueField S) n (e : ℤ) _
    (ramification_smul_restrict_residue_polynomialNorm_defect R p S n x hπ hϖ u e he q ε)
  simpa only [hd, Nat.cast_mul] using h

end MilnorK.PolynomialNorm
