/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.One
public import Aglib.KTheory.MilnorK.Residue.Product
public import Aglib.RingTheory.DVRNormValuation

/-!
# The actual norm–residue square on local-unit mixed symbols

The ordinary norm valuation theorem gives the full degree-one square and the
higher-degree square on a base DVR-unit prefix followed by one arbitrary
extension unit. The bottom norm uses an explicit actual primitive presentation
of the residue extension. No simplicity or separability of that extension is
inferred, and no residue characteristic-zero assumption is required.

The arbitrary-prefix and full higher-degree norm–residue square remain separate.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing

namespace DVR

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- A final arbitrary fraction-field unit after actual ring units contributes
its integer order, including negative orders and the empty prefix. -/
theorem residue_symbol_ring_units_snoc (m : ℕ) (a : Fin m → Rˣ) (b : Fˣ) :
    residue R F m (symbol (Fin.snoc (MilnorK.K2.DVR.fieldUnits R F ∘ a) b)) =
      MilnorK.K2.DVR.value R F (Additive.ofMul b) •
        symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [residue_eq R F hπ]
  have h := residue_symbol_snoc_units (MilnorK.K2.DVR.data (K := F) hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hπ) m (MilnorK.K2.DVR.fieldUnits R F ∘ a)
    (fun i => MilnorK.K2.DVR.value_fieldUnits R F (a i)) b
  rw [← specializeWithUniformizer, specializeWithUniformizer_ring_units] at h
  exact h

variable (S E : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E] [PerfectField F]

/-- The native ordinary norm valuation law is literally the order used by the
original Milnor DVR residue. No compatibility premise is supplied. -/
theorem value_norm (b : Eˣ) :
    MilnorK.K2.DVR.value R F (Additive.ofMul (Units.map (Algebra.norm F) b)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) *
        MilnorK.K2.DVR.value S E (Additive.ofMul b) :=
  IsDiscreteValuationRing.NormValuation.order_norm R S F E b

end DVR

namespace PolynomialNorm

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Algebra S (AdjoinRoot p.val)] [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]

/-- The full degree-one norm–residue square, expressed through the actual
integer identifications of both K₀ groups. -/
theorem zeroEquiv_residue_polynomialNorm_one (x : K (AdjoinRoot p.val) 1) :
    zeroEquiv (ResidueField R) (DVR.residue R F 0 (polynomialNorm 1 p x)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) *
        zeroEquiv (ResidueField S) (DVR.residue S (AdjoinRoot p.val) 0 x) := by
  let : FiniteDimensional F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
  rw [DVR.zeroEquiv_residue, oneEquiv_polynomialNorm, DVR.zeroEquiv_residue]
  exact DVR.value_norm R F S (AdjoinRoot p.val) (oneEquiv (AdjoinRoot p.val) x).toMul

/-- In every degree a genuine base-ring-unit prefix has norm residue equal to
the residue degree times the extension order and its literal reduced prefix. -/
theorem residue_polynomialNorm_ring_units (m : ℕ) (a : Fin m → Rˣ)
    (b : (AdjoinRoot p.val)ˣ) :
    DVR.residue R F m (polynomialNorm (m + 1) p
      (symbol (Fin.snoc
        (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
          (MilnorK.K2.DVR.fieldUnits R F ∘ a)) b))) =
      ((Module.finrank (ResidueField R) (ResidueField S) : ℤ) *
        MilnorK.K2.DVR.value S (AdjoinRoot p.val) (Additive.ofMul b)) •
          symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  let : FiniteDimensional F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
  rw [polynomialNorm_symbol_constants_unit, DVR.residue_symbol_ring_units_snoc,
    DVR.value_norm R F S (AdjoinRoot p.val)]

/-- The literal square on local-unit mixed symbols. The bottom polynomial and
algebra equivalence are explicit actual residue-field presentation data. -/
theorem residue_polynomialNorm_ring_units_eq (m : ℕ) (a : Fin m → Rˣ)
    (b : (AdjoinRoot p.val)ˣ) (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F m (polynomialNorm (m + 1) p
      (symbol (Fin.snoc
        (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
          (MilnorK.K2.DVR.fieldUnits R F ∘ a)) b))) =
      polynomialNorm m q (map m ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) m (symbol (Fin.snoc
          (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
            (MilnorK.K2.DVR.fieldUnits R F ∘ a)) b)))) := by
  have hfields : Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
      (MilnorK.K2.DVR.fieldUnits R F ∘ a) =
      MilnorK.K2.DVR.fieldUnits S (AdjoinRoot p.val) ∘
        (Units.map (algebraMap R S).toMonoidHom ∘ a) := by
    funext i
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply R F (AdjoinRoot p.val) (a i)).symm.trans
      (IsScalarTower.algebraMap_apply R S (AdjoinRoot p.val) (a i))
  have hres : Units.map (IsLocalRing.residue S).toMonoidHom ∘
      (Units.map (algebraMap R S).toMonoidHom ∘ a) =
      Units.map (algebraMap (ResidueField R) (ResidueField S)).toMonoidHom ∘
        (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
    funext i
    apply Units.ext
    exact (ResidueField.algebraMap_residue (R := R) (S := S) (a i : R)).symm
  have hdeg : q.val.natDegree = Module.finrank (ResidueField R) (ResidueField S) := by
    rw [← AdjoinRoot.powerBasis_dim q.property.2.ne_zero,
      ← (AdjoinRoot.powerBasis q.property.2.ne_zero).finrank]
    exact ε.toLinearEquiv.finrank_eq
  have hε : ε.symm.toRingHom.comp (algebraMap (ResidueField R) (ResidueField S)) =
      algebraMap (ResidueField R) (AdjoinRoot q.val) :=
    RingHom.ext fun x => ε.symm.commutes x
  have hmaps (x : K (ResidueField R) m) :
      map m ε.symm.toRingHom (map m (algebraMap (ResidueField R) (ResidueField S)) x) =
        map m (algebraMap (ResidueField R) (AdjoinRoot q.val)) x := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hε]
  rw [residue_polynomialNorm_ring_units R F p S, hfields,
    DVR.residue_symbol_ring_units_snoc, hres, ← map_symbol, map_smul,
    hmaps, map_smul, polynomialNorm_map_constants, hdeg]
  rw [smul_smul]
  exact congrArg (· • symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a))
    (mul_comm _ _)

/-- With an explicit residue presentation, the degree-one square holds on all
original quotient classes, rather than only their unit-symbol generators. -/
theorem residue_polynomialNorm_one_eq
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S)
    (x : K (AdjoinRoot p.val) 1) :
    DVR.residue R F 0 (polynomialNorm 1 p x) =
      polynomialNorm 0 q (map 0 ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) 0 x)) := by
  have h : (DVR.residue R F 0).comp (polynomialNorm 1 p) =
      (polynomialNorm 0 q).comp ((map 0 ε.symm.toRingHom).comp
        (DVR.residue S (AdjoinRoot p.val) 0)) := by
    apply linearMap_ext
    intro a
    have ha : a = Fin.snoc (Fin.elim0 : Fin 0 → (AdjoinRoot p.val)ˣ) (a 0) := by
      funext i
      have hi : i = Fin.last 0 := Subsingleton.elim _ _
      subst i
      rw [Fin.snoc_last]
      rfl
    have hempty : Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
        (MilnorK.K2.DVR.fieldUnits R F ∘ (Fin.elim0 : Fin 0 → Rˣ)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    simpa only [LinearMap.comp_apply, hempty, ← ha] using
      residue_polynomialNorm_ring_units_eq R F p S 0 Fin.elim0 (a 0) q ε
  exact LinearMap.congr_fun h x

end PolynomialNorm

end MilnorK
