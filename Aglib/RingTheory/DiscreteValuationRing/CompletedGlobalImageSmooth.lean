/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalTermination

/-!
# Smooth enlargement of an actual finite-type source in completed power series

For an abstract finite-type source embedded in the original completed
power-series ring, choose its native fraction field and extend the actual point
into the target fraction field. The finite generic degree is computed from the
original polynomial action. The global termination theorem then supplies a
finite-type enlarged source, still embedded in the same power-series ring,
whose actual π-centre is smooth. The intrinsic completed-fraction condition is
passed to that theorem; characteristic zero is retained as a thin wrapper.

Keeping the source abstract here avoids unfolding a concrete evaluation image
through the native fraction-field constructions in the selected-system
consumer. No separate source model or approximation premise is introduced.
-/

@[expose] public noncomputable section

open IsLocalRing Algebra.NeronModification

namespace PowerSeriesLocalization

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (n : ℕ) (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial (Fin n) R
local notation "C" => MvPowerSeries (Fin n) Rhat
local notation "A" => ParameterLocalization.Ring R (Fin n) p
local notation "S" => CompletedRing R (Fin n) p

local instance : IsDomain C := NoZeroDivisors.to_isDomain _
/-- The original polynomial ring acts on completed power series through the
coefficientwise polynomial inclusion. -/
local instance completedImageInclusionAlgebra : Algebra P C :=
  (completedPolynomialInclusion R (Fin n)).toAlgebra

variable {B : Type u} [CommRing B] [Algebra (MvPolynomial (Fin n) R) B]
  [Algebra.FiniteType (MvPolynomial (Fin n) R) B]

/-- An actual finite-type source in the original power-series ring has a
finite-type enlargement, still embedded there, smooth at its literal π-centre.
The native common fraction field and its generic degree are constructed in the
proof, rather than supplied as extra hypotheses to the image consumer. -/
theorem exists_completedGlobal_image_smoothCentre_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    (f : B →ₐ[P] C) (hinj : Function.Injective f) :
    ∃ (B' : CommAlgCat.{u} P) (φ : B →ₐ[P] B') (f' : B' →ₐ[P] C),
      Algebra.FiniteType P B' ∧ IsDomain B' ∧ Function.Injective f' ∧
      f'.comp φ = f ∧
      ∃ hq : (residueCentre (MvPolynomial.C p) f').IsPrime,
        letI := hq
        Algebra.IsSmoothAt P (residueCentre (MvPolynomial.C p) f') := by
  classical
  let : IsDomain B := Function.Injective.isDomain f hinj
  have hPC : Function.Injective (algebraMap P C) := by
    intro a b hab
    apply IsLocalization.injective A (Ideal.primeCompl_le_nonZeroDivisors
      (ParameterLocalization.parameterIdeal R (Fin n) p))
    apply completedPolynomialMap_injective R (Fin n) p
    rw [completedPolynomialMap_polynomial, completedPolynomialMap_polynomial]
    exact congrArg (algebraMap C S) hab
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr (by
    intro a b hab
    apply hPC
    simpa only [f.commutes] using congrArg f hab)
  let K := FractionRing B
  let : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  let : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  let J : B →+* FractionRing C := (algebraMap C (FractionRing C)).comp f.toRingHom
  have hJ : Function.Injective J := (IsFractionRing.injective C (FractionRing C)).comp hinj
  let j : K →+* FractionRing C :=
    IsFractionRing.lift («A» := B) (K := K) (g := J) hJ
  have hj : j.comp (algebraMap B K) = (algebraMap C (FractionRing C)).comp f.toRingHom := by
    apply RingHom.ext
    intro b
    exact IsFractionRing.lift_algebraMap («A» := B) (K := K) (g := J) hJ b
  let d := Cardinal.toNat (Algebra.trdeg P B)
  have hdB : Algebra.trdeg P B = (d : Cardinal) :=
    (Cardinal.cast_toNat_of_lt_aleph0
      (trdeg_lt_aleph0_of_finiteType (R := P) («S» := B))).symm
  let : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  let : Algebra.IsAlgebraic P (FractionRing P) :=
    IsLocalization.isAlgebraic (FractionRing P) (nonZeroDivisors P)
  have hBK : Algebra.trdeg P B = Algebra.trdeg P K := by
    simpa only [trdeg_eq_zero, add_zero] using trdeg_add_eq P B («A» := K)
  have hFK : Algebra.trdeg (FractionRing P) K = Algebra.trdeg P K := by
    simpa only [trdeg_eq_zero, zero_add] using trdeg_add_eq P (FractionRing P) («A» := K)
  have hd : Algebra.trdeg (FractionRing P) K = (d : Cardinal) :=
    hFK.trans (hBK.symm.trans hdB)
  obtain ⟨B', φ, f', k', hfin', hdom', hinj', hpoint, hfieldpoint, hfield, hj',
    htop, hq, hsmooth⟩ :=
    exists_completedGlobal_smoothCentre_of_geometricallyReducedFractionCompletion
      R n p K hcoeff f hinj j hj d hd
  exact ⟨B', φ, f', hfin', hdom', hinj', hpoint, hq, hsmooth⟩

variable [CharZero R]

/-- Characteristic zero supplies the intrinsic completed-fraction condition
for the same actual global construction. -/
theorem exists_completedGlobal_image_smoothCentre_of_charZero
    (f : B →ₐ[P] C) (hinj : Function.Injective f) :
    ∃ (B' : CommAlgCat.{u} P) (φ : B →ₐ[P] B') (f' : B' →ₐ[P] C),
      Algebra.FiniteType P B' ∧ IsDomain B' ∧ Function.Injective f' ∧
      f'.comp φ = f ∧
      ∃ hq : (residueCentre (MvPolynomial.C p) f').IsPrime,
        letI := hq
        Algebra.IsSmoothAt P (residueCentre (MvPolynomial.C p) f') := by
  exact exists_completedGlobal_image_smoothCentre_of_geometricallyReducedFractionCompletion R n p
    (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R) f hinj

end PowerSeriesLocalization
