/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompletePrime
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalCompletion
public import Aglib.RingTheory.PowerSeriesConstantClosure
public import Aglib.FieldTheory.AdjoinRootNormalScalarBranch

/-!
# The prime-normal constant norm over the complete power-series DVR

The complete local theorem is transported through the proved actual residue
field of the constant root closure. Both residue norms retain the original
polynomial presentation; no presentation independence or tower law is used.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial IsLocalRing Polynomial.LocalResidue PolynomialResidue
open PowerSeries.ConstantClosure

variable {k : Type*} [Field k]

/-- The literal residue-field presentation transported from the original coefficients. -/
def constantResiduePolynomial (p : MonicIrreducible k) :
    MonicIrreducible (ResidueField (PowerSeries k)) :=
  ⟨p.val.map PowerSeries.residueFieldOfPowerSeries.symm.toRingHom, p.property.1.map _, by
    let e : ResidueField (PowerSeries k) ≃+* k := PowerSeries.residueFieldOfPowerSeries
    change Irreducible ((Polynomial.mapEquiv e.symm) p.val)
    rw [MulEquiv.irreducible_iff]
    exact p.property.2⟩

/-- Mapping the residue presentation back gives the original polynomial literally. -/
theorem constantResiduePolynomial_map (p : MonicIrreducible k) :
    (constantResiduePolynomial p).val.map PowerSeries.residueFieldOfPowerSeries.toRingHom =
      p.val := by
  change (p.val.map PowerSeries.residueFieldOfPowerSeries.symm.toRingHom).map _ = _
  rw [Polynomial.map_map]
  simp

/-- Literal coefficient equivalence on the root presentations. -/
def constantResidueRootEquiv (p : MonicIrreducible k) :
    AdjoinRoot (constantResiduePolynomial p).val ≃+* AdjoinRoot p.val :=
  AdjoinRoot.mapRingEquiv PowerSeries.residueFieldOfPowerSeries
    (constantResiduePolynomial p).val p.val
    (by
      change Associated ((constantResiduePolynomial p).val.map
        PowerSeries.residueFieldOfPowerSeries.toRingHom) p.val
      rw [constantResiduePolynomial_map])

/-- Its forward map is the original quotient coefficient map. -/
theorem constantResidueRootEquiv_toRingHom (p : MonicIrreducible k) :
    (constantResidueRootEquiv p).toRingHom =
      adjoinRootMap PowerSeries.residueFieldOfPowerSeries.toRingHom
        (constantResiduePolynomial p).val p.val
        (by rw [constantResiduePolynomial_map]) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change AdjoinRoot.map PowerSeries.residueFieldOfPowerSeries.toRingHom
      (constantResiduePolynomial p).val p.val
      (by rw [constantResiduePolynomial_map])
      (AdjoinRoot.of (constantResiduePolynomial p).val a) = _
    rw [AdjoinRoot.map_of]
    exact (adjoinRootMap_algebraMap PowerSeries.residueFieldOfPowerSeries.toRingHom
      (constantResiduePolynomial p).val p.val
      (by rw [constantResiduePolynomial_map]) a).symm
  · change AdjoinRoot.map PowerSeries.residueFieldOfPowerSeries.toRingHom
      (constantResiduePolynomial p).val p.val
      (by rw [constantResiduePolynomial_map])
      (AdjoinRoot.root (constantResiduePolynomial p).val) = _
    rw [AdjoinRoot.map_root, adjoinRootMap_root]

variable [CharZero k]

local instance : CharZero (ResidueField (PowerSeries k)) :=
  RingHom.charZero (PowerSeries.residueFieldOfPowerSeries.toRingHom :
    ResidueField (PowerSeries k) →+* k)

/-- The residue presentation identifies with the actual closure residue field. -/
def constantResiduePresentationEquiv (p : MonicIrreducible k) :
    AdjoinRoot (constantResiduePolynomial p).val ≃ₐ[ResidueField (PowerSeries k)]
      ResidueField (Closure p) :=
  AlgEquiv.ofRingEquiv (f := (constantResidueRootEquiv p).trans
    (PowerSeries.ConstantClosure.residueEquiv p)) (by
    intro a
    change PowerSeries.ConstantClosure.residueEquiv p
      (constantResidueRootEquiv p (algebraMap _ _ a)) = _
    have hr := RingHom.congr_fun (constantResidueRootEquiv_toRingHom p)
      (algebraMap (ResidueField (PowerSeries k))
        (AdjoinRoot (constantResiduePolynomial p).val) a)
    change constantResidueRootEquiv p (algebraMap _ _ a) = _ at hr
    rw [hr, adjoinRootMap_algebraMap]
    rw [PowerSeries.ConstantClosure.residueEquiv_algebraMap]
    congr 1
    exact (PowerSeries.residueFieldOfPowerSeries :
      ResidueField (PowerSeries k) ≃+* k).symm_apply_apply a)

/-- Transport back to the original residue presentation cancels the two exact equivalences. -/
theorem constantResiduePresentationEquiv_symm_comp (p : MonicIrreducible k) :
    (adjoinRootMap PowerSeries.residueFieldOfPowerSeries.toRingHom
      (constantResiduePolynomial p).val p.val
      (by rw [constantResiduePolynomial_map])).comp
        (constantResiduePresentationEquiv p).symm.toRingHom =
      (PowerSeries.ConstantClosure.residueEquiv p).symm.toRingHom := by
  rw [← constantResidueRootEquiv_toRingHom]
  apply RingHom.ext
  intro x
  exact (constantResidueRootEquiv p).apply_symm_apply
    ((PowerSeries.ConstantClosure.residueEquiv p).symm x)

/-- The constant prime-normal norm commutes with the actual complete DVR
residue, expressed in the original coefficient root field. -/
theorem residue_polynomialNorm_laurent_constant
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ) (x : K (TopField p) (n + 1)) :
    map n PowerSeries.residueFieldOfPowerSeries.toRingHom
      (DVR.residue (PowerSeries k) (LaurentSeries k) n
        (polynomialNorm (n + 1) (constantPolynomial p) x)) =
      polynomialNorm n p
        (map n (PowerSeries.ConstantClosure.residueEquiv p).symm.toRingHom
          (DVR.residue (Closure p) (TopField p) n x)) := by
  let : Normal (LaurentSeries k) (TopField p) :=
    AdjoinRoot.normal_of_dvd_map p.property.1 dvd_rfl
  have hpF : (constantPolynomial p).val.natDegree.Prime := by
    change (p.val.map (algebraMap k (LaurentSeries k))).natDegree.Prime
    simpa only [Polynomial.natDegree_map] using hp
  have h := residue_polynomialNorm_complete_prime (PowerSeries k) (LaurentSeries k)
    (constantPolynomial p) hpF n x (constantResiduePolynomial p)
    (constantResiduePresentationEquiv p)
  rw [h, polynomialNorm_restrict_irreducible
    PowerSeries.residueFieldOfPowerSeries.toRingHom n
    (constantResiduePolynomial p) p (constantResiduePolynomial_map p).symm]
  change polynomialNorm n p (((map n _).comp (map n _)) _) = _
  rw [← map_comp, constantResiduePresentationEquiv_symm_comp]

end MilnorK.PolynomialNorm
