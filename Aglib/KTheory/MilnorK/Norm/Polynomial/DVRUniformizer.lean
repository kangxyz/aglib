/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRRingUnit
public import Aglib.RingTheory.DVRPrimeUniformizerNorm

/-!
# Prime-degree norm–residue compatibility with a final uniformizer

The exact native normalized norm coefficient feeds the original signed
all-degree residue recursion. Both ramification branches use the same formula;
the remaining sign comparison uses the actual two-torsion sign class. The
actual ring-unit/uniformizer decomposition then permits any last field unit,
including poles, while retaining an arbitrary base-field prefix.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing

namespace DVR

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The exact signed last-slot recursion extends from symbols to every prefix
class, with no valuation or integrality restriction on that prefix. -/
theorem residue_productUnit {π : R} (hπ : Irreducible π)
    (m : ℕ) (x : K F (m + 1)) (b : Fˣ) :
    residue R F (m + 1) (productUnit (m + 1) x (Additive.ofMul b)) =
      MilnorK.K2.DVR.value R F (Additive.ofMul b) •
          specializeWithUniformizer R F hπ (m + 1) x -
        productUnit m (residue R F m x)
          (MilnorK.K2.DVR.unitPart (K := F) hπ (Additive.ofMul b) -
            MilnorK.K2.DVR.value R F (Additive.ofMul b) •
              MilnorK.K2.residueSign (ResidueField R)) := by
  have h : (residue R F (m + 1)).comp
      ((productUnit (m + 1)).flip (Additive.ofMul b)) =
      MilnorK.K2.DVR.value R F (Additive.ofMul b) •
          specializeWithUniformizer R F hπ (m + 1) -
        ((productUnit m).flip (MilnorK.K2.DVR.unitPart (K := F) hπ (Additive.ofMul b) -
          MilnorK.K2.DVR.value R F (Additive.ofMul b) •
            MilnorK.K2.residueSign (ResidueField R))).comp (residue R F m) := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, productUnit_symbol]
    rw [residue_eq R F hπ (m + 1), residue_eq R F hπ m]
    exact residue_symbol_snoc (MilnorK.K2.DVR.data (K := F) hπ)
      (MilnorK.K2.DVR.unitReductionCompatible hπ) m a b
  exact LinearMap.congr_fun h x

/-- The original normalized residue-unit map of the ordinary uniformizer norm
has the exact native prime-degree coefficient, including its determinant sign. -/
theorem unitResidue_norm_uniformizer_prime
    (S E : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [HenselianLocalRing S] [Algebra R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]
    [PerfectField F] [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E] [FiniteDimensional F E]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime (Module.finrank F E)) :
    MilnorK.K2.DVR.unitResidue (K := F) hπ
        (Units.map (Algebra.norm F) (MilnorK.K2.DVR.uniformizer (K := E) hϖ)) =
      (-1 : (ResidueField R)ˣ) ^
          (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
        (Units.map (Algebra.norm (ResidueField R))
          (Units.map (IsLocalRing.residue S).toMonoidHom u))⁻¹ := by
  obtain ⟨b, hb, hbres⟩ :=
    IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree
      R S F E hπ hϖ u e he heunit hp
  have hnorm : Units.map (Algebra.norm F) (MilnorK.K2.DVR.uniformizer (K := E) hϖ) =
      MilnorK.K2.DVR.uniformizer (K := F) hπ ^
          Module.finrank (ResidueField R) (ResidueField S) * MilnorK.K2.DVR.fieldUnits R F b := by
    apply Units.ext
    change Algebra.norm F (algebraMap S E ϖ) =
      algebraMap R F π ^ Module.finrank (ResidueField R) (ResidueField S) * algebraMap R F (b : R)
    rw [← Algebra.algebraMap_intNorm (A := R) (K := F) (L := E), hb, map_mul, map_pow]
  rw [hnorm, map_mul, map_pow, MilnorK.K2.DVR.unitResidue_uniformizer,
    one_pow, one_mul, MilnorK.K2.DVR.unitResidue_fieldUnits]
  apply Units.ext
  simpa using hbres

end DVR

namespace PolynomialNorm

/-- A residue-field presentation transports the original mixed polynomial norm
formula through the actual algebra equivalence. -/
theorem polynomialNorm_productUnit_algEquiv {k l : Type*} [Field k] [Field l]
    [Algebra k l] [CharZero k] (m : ℕ) (q : MonicIrreducible k)
    (ε : AdjoinRoot q.val ≃ₐ[k] l) (x : K k m) (b : Additive lˣ) :
    polynomialNorm (m + 1) q (map (m + 1) ε.symm.toRingHom
      (productUnit m (map m (algebraMap k l) x) b)) =
        productUnit m x (Additive.ofMul (Units.map (Algebra.norm k) b.toMul)) := by
  have hε : ε.symm.toRingHom.comp (algebraMap k l) = algebraMap k (AdjoinRoot q.val) :=
    RingHom.ext fun a => ε.symm.commutes a
  have hmaps : map m ε.symm.toRingHom (map m (algebraMap k l) x) =
      map m (algebraMap k (AdjoinRoot q.val)) x := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hε]
  rw [map_productUnit, hmaps, polynomialNorm_productUnit_constants]
  congr 2
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv ε.symm (b.toMul : l)

private theorem uniformizer_residue_sign_algebra {k : Type*} [Field k]
    (m : ℕ) (x : K k m) (s : K k (m + 1)) (c : Additive kˣ) (e f : ℤ) :
    f • s - productUnit m x
        ((f * (e - 1)) • MilnorK.K2.residueSign k - c - f • MilnorK.K2.residueSign k) =
      f • s + productUnit m x c + e • productUnit m x (f • MilnorK.K2.residueSign k) := by
  have ht : productUnit m x (MilnorK.K2.residueSign k) +
      productUnit m x (MilnorK.K2.residueSign k) = 0 := by
    rw [← map_add, MilnorK.K2.residueSign_add_self, map_zero]
  have htwo : (2 : ℤ) • productUnit m x (MilnorK.K2.residueSign k) = 0 := by
    simpa only [two_smul] using ht
  calc
    _ = f • s + productUnit m x c + e • productUnit m x (f • MilnorK.K2.residueSign k) -
        (f * (e - 1)) • ((2 : ℤ) • productUnit m x (MilnorK.K2.residueSign k)) := by
      simp only [map_sub, map_smul]
      module
    _ = _ := by rw [htwo, smul_zero, sub_zero]

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [HenselianLocalRing S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)] [CharZero (ResidueField R)]
  [Algebra S (AdjoinRoot p.val)] [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]

/-- The prime-degree norm–residue square for an arbitrary base-field prefix
and the actual extension uniformizer. The residue presentation stays explicit. -/
theorem residue_polynomialNorm_final_uniformizer (n : ℕ) (x : K F n)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime p.val.natDegree)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F n (polynomialNorm (n + 1) p
      (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
        (Additive.ofMul (MilnorK.K2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ)))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n
          (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
            (Additive.ofMul (MilnorK.K2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ))))) := by
  cases n with
  | zero => exact residue_polynomialNorm_one_eq R F p S q ε _
  | succ m =>
    let : FiniteDimensional F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
    let f := Module.finrank (ResidueField R) (ResidueField S)
    have hprime : Nat.Prime (Module.finrank F (AdjoinRoot p.val)) := by
      rwa [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    have hepos := MilnorK.K2.DVR.ramificationIndex_pos (algebraMap R S) hπ u e he
    have hf (r : R) : algebraMap F (AdjoinRoot p.val) (algebraMap R F r) =
        algebraMap S (AdjoinRoot p.val) (algebraMap R S r) :=
      (IsScalarTower.algebraMap_apply R F (AdjoinRoot p.val) r).symm.trans
        (IsScalarTower.algebraMap_apply R S (AdjoinRoot p.val) r)
    have hκ : IsLocalRing.ResidueField.map (algebraMap R S) =
        algebraMap (ResidueField R) (ResidueField S) := by
      ext a
      obtain ⟨r, rfl⟩ := residue_surjective a
      rfl
    have hr := DVR.residue_ramified_restrict_apply (algebraMap R S)
      (algebraMap F (AdjoinRoot p.val)) hf hπ hϖ u e he m x
    have hs := LinearMap.congr_fun (DVR.specialize_ramified_restrict (algebraMap R S)
      (algebraMap F (AdjoinRoot p.val)) hf hπ hϖ u e he m) x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.flip_apply] at hs
    rw [hκ] at hr hs
    have hvalue : MilnorK.K2.DVR.value R F (Additive.ofMul
        (Units.map (Algebra.norm F) (MilnorK.K2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ))) =
        (f : ℤ) := by
      rw [DVR.value_norm R F S (AdjoinRoot p.val), MilnorK.K2.DVR.value_uniformizer, mul_one]
    have hunit : MilnorK.K2.DVR.unitPart (K := F) hπ (Additive.ofMul
        (Units.map (Algebra.norm F) (MilnorK.K2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ))) =
        ((f : ℤ) * ((e : ℤ) - 1)) • MilnorK.K2.residueSign (ResidueField R) -
          Additive.ofMul (Units.map (Algebra.norm (ResidueField R))
            (Units.map (IsLocalRing.residue S).toMonoidHom u)) := by
      have h := congrArg Additive.ofMul (DVR.unitResidue_norm_uniformizer_prime R F
        S (AdjoinRoot p.val) hπ hϖ u e he heunit hprime)
      change Additive.ofMul (MilnorK.K2.DVR.unitResidue (K := F) hπ
        (Units.map (Algebra.norm F) (MilnorK.K2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ))) = _
      simpa only [f, MilnorK.K2.residueSign, ofMul_mul, ofMul_pow, ofMul_inv, ← natCast_zsmul,
        Nat.cast_mul, Nat.cast_sub hepos, Nat.cast_one, sub_eq_add_neg] using h
    have hqdeg : q.val.natDegree = f := by
      rw [← AdjoinRoot.powerBasis_dim q.property.2.ne_zero,
        ← (AdjoinRoot.powerBasis q.property.2.ne_zero).finrank]
      exact ε.toLinearEquiv.finrank_eq
    have hε : ε.symm.toRingHom.comp (algebraMap (ResidueField R) (ResidueField S)) =
        algebraMap (ResidueField R) (AdjoinRoot q.val) :=
      RingHom.ext fun a => ε.symm.commutes a
    have hconst (y : K (ResidueField R) (m + 1)) :
        polynomialNorm (m + 1) q (map (m + 1) ε.symm.toRingHom
          (map (m + 1) (algebraMap (ResidueField R) (ResidueField S)) y)) = (f : ℤ) • y := by
      have hmaps : map (m + 1) ε.symm.toRingHom
          (map (m + 1) (algebraMap (ResidueField R) (ResidueField S)) y) =
          map (m + 1) (algebraMap (ResidueField R) (AdjoinRoot q.val)) y := by
        rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hε]
      rw [hmaps, polynomialNorm_map_constants, hqdeg]
    have hsign : Units.map (Algebra.norm (ResidueField R)) (-1 : (ResidueField S)ˣ) =
        (-1 : (ResidueField R)ˣ) ^ f := by
      apply Units.ext
      change Algebra.norm (ResidueField R) (-1 : ResidueField S) = (-1 : ResidueField R) ^ f
      simpa only [map_neg, map_one] using
        Algebra.norm_algebraMap (R := ResidueField R) (S := ResidueField S) (-1)
    rw [polynomialNorm_productUnit_constants, toMul_ofMul,
      DVR.residue_productUnit R F hπ, hvalue, hunit,
      DVR.residue_productUnit S (AdjoinRoot p.val) hϖ]
    simp only [MilnorK.K2.DVR.value_uniformizer, MilnorK.K2.DVR.unitPart_uniformizer,
      one_smul, zero_sub, map_neg, sub_neg_eq_add]
    rw [hs, hr]
    simp only [map_add, map_smul, LinearMap.smul_apply]
    rw [hconst, polynomialNorm_productUnit_algEquiv,
      polynomialNorm_productUnit_algEquiv]
    simp only [MilnorK.K2.DVR.ramificationUnitResidue, MilnorK.K2.residueSign, toMul_ofMul,
      hsign, ofMul_pow]
    simpa only [MilnorK.K2.residueSign, natCast_zsmul] using
      uniformizer_residue_sign_algebra m (DVR.residue R F m x)
        (DVR.specializeWithUniformizer R F hπ (m + 1) x)
        (Additive.ofMul (Units.map (Algebra.norm (ResidueField R))
          (Units.map (IsLocalRing.residue S).toMonoidHom u))) (e : ℤ) (f : ℤ)

/-- The final coordinate may be any actual extension-field unit, with arbitrary
integer order. Its genuine ring-unit/uniformizer decomposition closes the mixed square. -/
theorem residue_polynomialNorm_mixed_prime (n : ℕ) (x : K F n)
    (b : (AdjoinRoot p.val)ˣ)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime p.val.natDegree)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F n (polynomialNorm (n + 1) p
      (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n
          (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b)))) := by
  have hb := congrArg Additive.ofMul (MilnorK.K2.DVR.normalizedLift_decomposition hϖ b)
  rw [hb]
  simp only [ofMul_mul, ofMul_zpow, map_add, map_smul]
  rw [residue_polynomialNorm_final_ring_unit R F p S n x _ hπ hϖ u e he q ε,
    residue_polynomialNorm_final_uniformizer R F p S n x hπ hϖ u e he heunit hp q ε]

end PolynomialNorm

end MilnorK
