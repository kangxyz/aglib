/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRDefect
public import Aglib.KTheory.MilnorK.Norm.Polynomial.CoprimeRootSquare
public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRQuadratic
public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRCoprimeBaseChange

/-!
# Actual mixed valuation descent of the tame norm-residue defect

The two vertical ramified restriction formulas, singleton polynomial norm base
change, and the proved mixed square over the upper DVR identify the restricted
defect. All ring maps, root-field maps, uniformizer equations and the residue
root-field equivalence are literal. No norm-defect compatibility is a premise.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing

private theorem residueAlgebraMap_eq_map {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    algebraMap (ResidueField R) (ResidueField S) = ResidueField.map (algebraMap R S) := by
  ext x
  obtain ⟨r, rfl⟩ := residue_surjective x
  rfl

variable {F L : Type*} [Field F] [Field L] [CharZero F] [CharZero L]
  [Algebra F L] [Module.Finite F L]
  (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R F] [IsFractionRing R F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Algebra S (AdjoinRoot p.val)] [IsFractionRing S (AdjoinRoot p.val)]
  (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R T] [IsLocalHom (algebraMap R T)]
  [Algebra T L] [IsFractionRing T L] [Algebra R L]
  [IsScalarTower R F L] [IsScalarTower R T L]
  (pL : MonicIrreducible L) (hpL : pL.val = p.val.map (algebraMap F L))
  (U : Type*) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
  [HenselianLocalRing U] [Algebra S U] [Algebra T U] [Algebra R U]
  [IsLocalHom (algebraMap S U)] [IsLocalHom (algebraMap T U)]
  [IsLocalHom (algebraMap R U)]
  [IsScalarTower R S U] [IsScalarTower R T U]
  [Algebra U (AdjoinRoot pL.val)] [IsFractionRing U (AdjoinRoot pL.val)]
  [IsScalarTower T U (AdjoinRoot pL.val)] [IsIntegralClosure U T (AdjoinRoot pL.val)]
  [Module.Finite T U] [Module.IsTorsionFree T U]
  [CharZero (ResidueField R)] [CharZero (ResidueField T)]
  [Module.Finite R T]

/-- The literal scalar-extension root-field map commutes with the two DVR maps. -/
def scalarRootMap : AdjoinRoot p.val →+* AdjoinRoot pL.val :=
  adjoinRootMap (algebraMap F L) p.val pL.val (hpL ▸ dvd_rfl)

omit [Module.Finite F L] in
/-- Mixedness only in the upper field suffices to kill the restricted defect
by the common vertical ramification exponent. Its equality on the two sides is
recorded by the two actual uniformizer equations, not by a norm law. -/
theorem ramification_smul_restrict_defect_of_mixed
    (hfield : ∀ s : S, scalarRootMap p pL hpL (algebraMap S (AdjoinRoot p.val) s) =
      algebraMap U (AdjoinRoot pL.val) (algebraMap S U s))
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    (hx : map (n + 1) (scalarRootMap p pL hpL) x ∈
      mixedSpan (algebraMap L (AdjoinRoot pL.val)) n)
    {π : R} {ϖ : S} {τ : T} {υ : U}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (hτ : Irreducible τ) (hυ : Irreducible υ)
    (v : Tˣ) (a : ℕ) (hRT : algebraMap R T π = (v : T) * τ ^ a)
    (w : Uˣ) (hSU : algebraMap S U ϖ = (w : U) * υ ^ a)
    (u : Uˣ) (c : ℕ) (hTU : algebraMap T U τ = (u : U) * υ ^ c)
    (hcunit : IsUnit (c : U)) (hp : p.val.natDegree.Prime)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S)
    (hcopq : q.val.natDegree.Coprime
      (Module.finrank (ResidueField R) (ResidueField T)))
    (hdegree : Module.finrank (ResidueField T) (ResidueField U) = q.val.natDegree) :
    (a : ℤ) • map n (algebraMap (ResidueField R) (ResidueField T))
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue S (AdjoinRoot p.val) n x))) = 0 := by
  let qT := coprimeCoefficientPolynomial q hcopq
  let εT := coprimeRootAlgEquiv q hcopq ε hdegree
  have htop : DVR.residue T L n
      (polynomialNorm (n + 1) pL (map (n + 1) (scalarRootMap p pL hpL) x)) =
      polynomialNorm n qT (map n εT.symm.toRingHom
        (DVR.residue U (AdjoinRoot pL.val) n
          (map (n + 1) (scalarRootMap p pL hpL) x))) := by
    apply residue_polynomialNorm_of_mem_mixedSpan T L pL U n _ hx
      hτ hυ u c hTU hcunit
    · simpa only [hpL, Polynomial.natDegree_map] using hp
  have hnorm := polynomialNorm_restrict_irreducible (algebraMap F L) (n + 1) p pL hpL x
  have hR := DVR.residue_ramified_restrict_apply (algebraMap R T) (algebraMap F L)
    (fun r => by simp only [← IsScalarTower.algebraMap_apply]) hπ hτ v a hRT n
    (polynomialNorm (n + 1) p x)
  have hS := DVR.residue_ramified_restrict_apply (algebraMap S U)
    (scalarRootMap p pL hpL) hfield hϖ hυ w a hSU n x
  rw [← residueAlgebraMap_eq_map] at hR hS
  rw [map_sub, smul_sub, sub_eq_zero]
  calc
    _ = DVR.residue T L n (map (n + 1) (algebraMap F L)
        (polynomialNorm (n + 1) p x)) := hR.symm
    _ = _ := by
      rw [hnorm]
      change DVR.residue T L n
        (polynomialNorm (n + 1) pL (map (n + 1) (scalarRootMap p pL hpL) x)) = _
      rw [htop, hS, map_smul, map_smul]
      exact congrArg ((a : ℤ) • ·)
        (polynomialNorm_coprime_root_square n q hcopq ε hdegree
          (DVR.residue S (AdjoinRoot p.val) n x)).symm

variable [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsScalarTower R S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  [Normal F (AdjoinRoot p.val)]
  [Module.IsTorsionFree R T] [IsIntegralClosure T R L]
  [Module.Finite S U] [Module.IsTorsionFree S U]
  [Algebra (AdjoinRoot p.val) (AdjoinRoot pL.val)]
  [Algebra S (AdjoinRoot pL.val)]
  [IsScalarTower S (AdjoinRoot p.val) (AdjoinRoot pL.val)]
  [IsScalarTower S U (AdjoinRoot pL.val)]
  [IsScalarTower F (AdjoinRoot p.val) (AdjoinRoot pL.val)]
  [IsIntegralClosure U S (AdjoinRoot pL.val)]

/-- In an actual finite coprime scalar-extension DVR square, upper mixedness
proves the full original all-class norm-residue equality. Opposite ramification
and residue degrees are derived from the four literal equations and field
degree formulas, rather than supplied as compatibility hypotheses. -/
theorem residue_polynomialNorm_of_coprime_mixed_diagram
    (hscalar : algebraMap (AdjoinRoot p.val) (AdjoinRoot pL.val) = scalarRootMap p pL hpL)
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    (hx : map (n + 1) (scalarRootMap p pL hpL) x ∈
      mixedSpan (algebraMap L (AdjoinRoot pL.val)) n)
    {π : R} {ϖ : S} {τ : T} {υ : U}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (hτ : Irreducible τ) (hυ : Irreducible υ)
    (u : Sˣ) (v : Tˣ) (w z : Uˣ) (e a b c : ℕ)
    (hRS : algebraMap R S π = (u : S) * ϖ ^ e)
    (hRT : algebraMap R T π = (v : T) * τ ^ a)
    (hSU : algebraMap S U ϖ = (w : U) * υ ^ b)
    (hTU : algebraMap T U τ = (z : U) * υ ^ c)
    (hcunit : IsUnit (c : U)) (hp : p.val.natDegree.Prime)
    (hcop : p.val.natDegree.Coprime (Module.finrank F L))
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F n (polynomialNorm (n + 1) p x) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n x)) := by
  let : CharZero (AdjoinRoot p.val) :=
    charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective
  let : Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
  let : Module.Finite L (AdjoinRoot pL.val) := pL.property.1.finite_adjoinRoot
  let : Module.Finite F (AdjoinRoot pL.val) := Module.Finite.trans L (AdjoinRoot pL.val)
  let : Module.Finite (AdjoinRoot p.val) (AdjoinRoot pL.val) :=
    Module.Finite.of_restrictScalars_finite F (AdjoinRoot p.val) (AdjoinRoot pL.val)
  have hd : Module.finrank F (AdjoinRoot p.val) = p.val.natDegree := by
    rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hdL : Module.finrank L (AdjoinRoot pL.val) = Module.finrank F (AdjoinRoot p.val) := by
    rw [hd, (AdjoinRoot.powerBasis pL.property.2.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hpL, Polynomial.natDegree_map]
  have hcomm : (algebraMap S U).comp (algebraMap R S) =
      (algebraMap T U).comp (algebraMap R T) := by
    rw [← IsScalarTower.algebraMap_eq R S U, ← IsScalarTower.algebraMap_eq R T U]
  obtain ⟨_, hba, hres, _⟩ := ramification_residue_finrank_eq_of_coprime_baseChange
    R S T U F (AdjoinRoot p.val) L (AdjoinRoot pL.val) hcomm hdL
    (by simpa only [hd] using hcop) hπ hϖ hτ hυ u v w z e a b c hRS hRT hSU hTU
  have hqdegree : q.val.natDegree = Module.finrank (ResidueField R) (ResidueField S) := by
    rw [← AdjoinRoot.powerBasis_dim q.property.2.ne_zero,
      ← (AdjoinRoot.powerBasis q.property.2.ne_zero).finrank]
    exact ε.toLinearEquiv.finrank_eq
  have hRSdegree := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F (AdjoinRoot p.val) hπ hϖ u e hRS
  have hRTdegree := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R T F L hπ hτ v a hRT
  have hcopq : q.val.natDegree.Coprime
      (Module.finrank (ResidueField R) (ResidueField T)) := by
    rw [hqdegree]
    apply hcop.of_dvd_left
      (show Module.finrank (ResidueField R) (ResidueField S) ∣ p.val.natDegree by
        rw [← hd, hRSdegree]; exact dvd_mul_left _ _)
      |>.of_dvd_right
        (show Module.finrank (ResidueField R) (ResidueField T) ∣ Module.finrank F L by
          rw [hRTdegree]; exact dvd_mul_left _ _)
  have hrestricted := ramification_smul_restrict_defect_of_mixed R p S T pL hpL U
    (fun s => by rw [← hscalar, ← IsScalarTower.algebraMap_apply S (AdjoinRoot p.val)
      (AdjoinRoot pL.val), IsScalarTower.algebraMap_apply S U (AdjoinRoot pL.val)])
    n x hx hπ hϖ hτ hυ v a hRT w (by simpa only [hba] using hSU)
    z c hTU hcunit hp q ε hcopq (hres.trans hqdegree.symm)
  have hsecond := mul_finrank_smul_eq_zero_of_smul_map_eq_zero
    (ResidueField R) (ResidueField T) n (a : ℤ) _ hrestricted
  have hsecond' : (Module.finrank F L : ℤ) •
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue S (AdjoinRoot p.val) n x))) = 0 := by
    simpa only [hRTdegree, Nat.cast_mul] using hsecond
  have hfirst := degree_smul_residue_polynomialNorm_defect R p S n x hπ hϖ u e hRS q ε
  apply sub_eq_zero.mp
  let y : K (ResidueField R) n :=
    DVR.residue R F n (polynomialNorm (n + 1) p x) -
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n x))
  change y = 0
  change (p.val.natDegree : ℤ) • y = 0 at hfirst
  change (Module.finrank F L : ℤ) • y = 0 at hsecond'
  obtain ⟨i, j, hij⟩ := hcop.isCoprime
  calc
    y = (1 : ℤ) • y := (one_smul ℤ y).symm
    _ = (i * (p.val.natDegree : ℤ) + j * (Module.finrank F L : ℤ)) • y := by rw [hij]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, hfirst, hsecond',
      smul_zero, smul_zero, add_zero]

end MilnorK.PolynomialNorm
