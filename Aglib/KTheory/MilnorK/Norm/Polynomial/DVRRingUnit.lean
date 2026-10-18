/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRUnits
public import Aglib.KTheory.MilnorK.Residue.RamifiedRestriction
public import Aglib.RingTheory.DVRNormResidueUnit

/-!
# Ramified norm–residue compatibility with a final ring unit

An arbitrary base-field Milnor class, including poles and repeated
uniformizers, may precede the final actual extension ring unit. Ramified
restriction contributes the uniformizer exponent to the residue prefix;
actual unit-norm reduction contributes exactly the same exponent to the last
unit. The original signed residue recursion gives the square.

The bottom mixed-norm formula currently requires characteristic zero of the
base residue field, which is explicit. The final extension-uniformizer case
and arbitrary higher-degree classes remain separate.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing

namespace DVR

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual signed recursion for an arbitrary prefix and final ring unit. -/
theorem residue_productUnit_ring_unit (m : ℕ) (x : K F (m + 1)) (b : Rˣ) :
    residue R F (m + 1)
      (productUnit (m + 1) x (Additive.ofMul (MilnorK.K2.DVR.fieldUnits R F b))) =
        -productUnit m (residue R F m x)
          (Additive.ofMul (Units.map (IsLocalRing.residue R).toMonoidHom b)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h : (residue R F (m + 1)).comp
      ((productUnit (m + 1)).flip (Additive.ofMul (MilnorK.K2.DVR.fieldUnits R F b))) =
      -((productUnit m).flip (Additive.ofMul
        (Units.map (IsLocalRing.residue R).toMonoidHom b))).comp (residue R F m) := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.flip_apply,
      productUnit_symbol]
    rw [residue_eq R F hπ (m + 1), residue_eq R F hπ m]
    change MilnorK.residue (MilnorK.K2.DVR.data (K := F) hπ) _ (m + 1)
      (symbol (Fin.snoc a (MilnorK.K2.DVR.fieldUnits R F b))) = _
    rw [residue_symbol_snoc]
    simp only [unitPartTwist_apply, MilnorK.K2.DVR.data,
      MilnorK.K2.DVR.value_fieldUnits, zero_smul, sub_zero, zero_sub]
    change -productUnit m _ (Additive.ofMul
      (MilnorK.K2.DVR.unitResidue (K := F) hπ (MilnorK.K2.DVR.fieldUnits R F b))) = _
    rw [MilnorK.K2.DVR.unitResidue_fieldUnits]
    rfl
  exact LinearMap.congr_fun h x

end DVR

namespace PolynomialNorm

private theorem polynomialNorm_productUnit_equiv {k l : Type*} [Field k] [Field l]
    [Algebra k l] [CharZero k] (m : ℕ) (q : MonicIrreducible k)
    (ε : AdjoinRoot q.val ≃ₐ[k] l) (x : K k m) (b : lˣ) :
    polynomialNorm (m + 1) q (map (m + 1) ε.symm.toRingHom
      (productUnit m (map m (algebraMap k l) x) (Additive.ofMul b))) =
        productUnit m x (Additive.ofMul (Units.map (Algebra.norm k) b)) := by
  have hε : ε.symm.toRingHom.comp (algebraMap k l) = algebraMap k (AdjoinRoot q.val) :=
    RingHom.ext fun a => ε.symm.commutes a
  have hmaps : map m ε.symm.toRingHom (map m (algebraMap k l) x) =
      map m (algebraMap k (AdjoinRoot q.val)) x := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hε]
  rw [map_productUnit, hmaps, polynomialNorm_productUnit_constants]
  congr 2
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv ε.symm (b : l)

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)] [CharZero (ResidueField R)]
  [Algebra S (AdjoinRoot p.val)] [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]

/-- The actual ramified square for every base-field prefix class and a final
actual extension ring unit. The empty prefix is the full degree-one square. -/
theorem residue_polynomialNorm_final_ring_unit (n : ℕ) (x : K F n) (b : Sˣ)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F n (polynomialNorm (n + 1) p
      (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
        (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b)))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n
          (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
            (Additive.ofMul (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b))))) := by
  cases n with
  | zero => exact residue_polynomialNorm_one_eq R F p S q ε _
  | succ m =>
    let : FiniteDimensional F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
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
    rw [hκ] at hr
    have hn : Additive.ofMul (Units.map (Algebra.norm F)
        (MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) b)) =
        Additive.ofMul (MilnorK.K2.DVR.fieldUnits R F (Units.map (Algebra.intNorm R S) b)) :=
      congrArg Additive.ofMul
        (IsDiscreteValuationRing.NormValuation.norm_ringUnit R S F (AdjoinRoot p.val) b)
    have hu := congrArg Additive.ofMul
      (Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he b)
    rw [polynomialNorm_productUnit_constants, toMul_ofMul, hn,
      DVR.residue_productUnit_ring_unit, hu,
      DVR.residue_productUnit_ring_unit, hr]
    simp only [ofMul_pow, map_neg, map_smul, LinearMap.smul_apply]
    rw [polynomialNorm_productUnit_equiv, map_nsmul, natCast_zsmul]

end PolynomialNorm

end MilnorK
