/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.ResidueCompletionIso
public import Aglib.RingTheory.AdicCompletion.IdealCongr
public import Aglib.RingTheory.Smooth.RegularKernel
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RingHom.Etale

/-! # Original completions in split etale coordinates

The original polynomial coordinates and augmentation construct the power-series
comparison. Every quotient comparison is produced by formal lifting; the
coefficient ring need not be complete. The smooth coordinate producer constructs
the coordinates internally over a
local coefficient ring, giving the original section-adic completion theorem.
-/

@[expose] public noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Constant coefficient as an algebra map over the original coefficient ring. -/
def zeroSectionAlgHom : MvPolynomial σ R →ₐ[R] R :=
  { constantCoeff with commutes' r := constantCoeff_C σ r }

/-- The original polynomial variable ideal is exactly its augmentation kernel. -/
theorem idealOfVars_eq_ker_zeroSection :
    idealOfVars σ R = RingHom.ker (zeroSectionAlgHom (σ := σ) (R := R)).toRingHom := by
  ext p
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff']
  change (∀ d, d.degree < 1 → p.coeff d = 0) ↔ p.coeff 0 = 0
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have he : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
    simpa only [he] using h

/-- The original zero-section quotient, retaining the actual constant coefficient. -/
def zeroSectionQuotientEquiv : (MvPolynomial σ R ⧸ idealOfVars σ R) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R idealOfVars_eq_ker_zeroSection).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (show Function.Surjective (zeroSectionAlgHom (σ := σ) (R := R)) from
        fun r => ⟨C r, constantCoeff_C σ r⟩))

@[simp] theorem zeroSectionQuotientEquiv_mk (p : MvPolynomial σ R) :
    zeroSectionQuotientEquiv (Ideal.Quotient.mk (idealOfVars σ R) p) = constantCoeff p := by
  rfl

end MvPolynomial

namespace Algebra.Smooth

open MvPolynomial

variable {R B σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (ε : B →ₐ[R] R) (x : σ → RingHom.ker ε.toRingHom)

/-- The original coordinate polynomial map, using elements of the original kernel. -/
def splitCoordinateMap : MvPolynomial σ R →ₐ[R] B :=
  MvPolynomial.aeval (fun i => (x i).val)

/-- The complete original coordinate-augmentation square. -/
theorem splitCoordinateMap_augmentation :
    ε.comp (splitCoordinateMap ε x) = MvPolynomial.zeroSectionAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, splitCoordinateMap, aeval_X]
  rw [show MvPolynomial.zeroSectionAlgHom (X i : MvPolynomial σ R) = 0 from
    MvPolynomial.constantCoeff_X R i]
  exact (x i).property

section CoordinateAlgebra

variable [Finite σ]

/-- Original split etale coordinates give the original section-adic completion.
The equivalence is constructed from the literal coordinate maps at every order. -/
def splitCoordinateCompletionData
    (h : (splitCoordinateMap ε x).toRingHom.FormallyEtale) :
    { e : MvPowerSeries σ R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B //
      ∀ p : MvPolynomial σ R, e (algebraMap _ (MvPowerSeries σ R) p) =
        algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B)
          (splitCoordinateMap ε x p) } := by
  let : Algebra (MvPolynomial σ R) B := (splitCoordinateMap ε x).toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) B :=
    IsScalarTower.of_algebraMap_eq' (splitCoordinateMap ε x).comp_algebraMap.symm
  let : Algebra.FormallyEtale (MvPolynomial σ R) B := h
  let g : B →ₐ[MvPolynomial σ R] MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R :=
    { (MvPolynomial.zeroSectionQuotientEquiv.symm.toAlgHom.comp ε).toRingHom with
      commutes' p := by
        apply MvPolynomial.zeroSectionQuotientEquiv.injective
        change MvPolynomial.zeroSectionQuotientEquiv
            (MvPolynomial.zeroSectionQuotientEquiv.symm (ε ((splitCoordinateMap ε x) p))) =
          MvPolynomial.zeroSectionQuotientEquiv
            (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R) p)
        rw [AlgEquiv.apply_symm_apply, MvPolynomial.zeroSectionQuotientEquiv_mk]
        exact AlgHom.congr_fun (splitCoordinateMap_augmentation ε x) p }
  have hg : RingHom.ker g.toRingHom = RingHom.ker ε.toRingHom :=
    RingHom.ker_comp_of_injective ε.toRingHom MvPolynomial.zeroSectionQuotientEquiv.symm.injective
  let e := Algebra.FormallyEtale.residueCompletionAlgEquiv (MvPolynomial.idealOfVars σ R) g
  rw [hg] at e
  let c := (MvPowerSeries.toAdicCompletionAlgEquiv σ R).trans e
  refine ⟨c.restrictScalars R, ?_⟩
  intro p
  exact c.commutes p

/-- The original split-coordinate completion equivalence from its whole-map construction. -/
def splitCoordinateCompletionAlgEquiv
    (h : (splitCoordinateMap ε x).toRingHom.FormallyEtale) :
    MvPowerSeries σ R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B :=
  (splitCoordinateCompletionData ε x h).val

/-- Every original polynomial coordinate is retained by the completion equivalence. -/
theorem splitCoordinateCompletionAlgEquiv_polynomial
    (h : (splitCoordinateMap ε x).toRingHom.FormallyEtale) (p : MvPolynomial σ R) :
    splitCoordinateCompletionAlgEquiv ε x h (algebraMap _ (MvPowerSeries σ R) p) =
      algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B)
        (splitCoordinateMap ε x p) :=
  (splitCoordinateCompletionData ε x h).property p

/-- The constructed comparison preserves the original coefficient inclusion. -/
theorem splitCoordinateCompletionAlgEquiv_C
    (h : (splitCoordinateMap ε x).toRingHom.FormallyEtale) (r : R) :
    splitCoordinateCompletionAlgEquiv ε x h (MvPowerSeries.C r) =
      algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) (algebraMap R B r) := by
  exact (splitCoordinateCompletionAlgEquiv ε x h).commutes r

end CoordinateAlgebra

section Away

variable (r : B) (hr : IsUnit (ε r))

/-- The original section extends over a principal neighbourhood along itself. -/
def splitAwayAugmentation : Localization.Away r →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom r hr

@[simp] theorem splitAwayAugmentation_algebraMap (b : B) :
    splitAwayAugmentation ε r hr (algebraMap B (Localization.Away r) b) = ε b :=
  IsLocalization.Away.lift_eq r hr b

/-- The original section is surjective onto its coefficient ring. -/
theorem splitSection_surjective : Function.Surjective ε :=
  fun a => ⟨algebraMap R B a, ε.commutes a⟩

/-- The original section identifies its actual kernel quotient with the base. -/
def splitSectionQuotientEquiv : (B ⧸ RingHom.ker ε.toRingHom) ≃ₐ[R] R :=
  Ideal.quotientKerAlgEquivOfSurjective (splitSection_surjective ε)

@[simp] theorem splitSectionQuotientEquiv_mk (b : B) :
    splitSectionQuotientEquiv ε (Ideal.Quotient.mk (RingHom.ker ε.toRingHom) b) = ε b :=
  Ideal.quotientKerAlgEquivOfSurjective_mk (splitSection_surjective ε) b

include hr in
/-- The original localized denominator is already a unit in the section quotient. -/
theorem splitSectionQuotient_isUnit :
    IsUnit (Ideal.Quotient.mk (RingHom.ker ε.toRingHom) r) := by
  have h := hr.map (splitSectionQuotientEquiv ε).symm.toRingHom
  change IsUnit ((splitSectionQuotientEquiv ε).symm (ε r)) at h
  rw [← splitSectionQuotientEquiv_mk ε r, AlgEquiv.symm_apply_apply] at h
  exact h

/-- The native localized section map into the original kernel quotient. -/
def splitAwayResidueMap : Localization.Away r →ₐ[B] B ⧸ RingHom.ker ε.toRingHom :=
  IsLocalization.Away.liftAlgHom
    (f := Ideal.Quotient.mkₐ B (RingHom.ker ε.toRingHom)) r (splitSectionQuotient_isUnit ε r hr)

/-- The entire localized residue square retains the original section. -/
theorem splitAwayResidueMap_comp :
    (splitSectionQuotientEquiv ε).toRingHom.comp (splitAwayResidueMap ε r hr).toRingHom =
      (splitAwayAugmentation ε r hr).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext b
  change splitSectionQuotientEquiv ε
      (splitAwayResidueMap ε r hr (algebraMap B (Localization.Away r) b)) =
    splitAwayAugmentation ε r hr (algebraMap B (Localization.Away r) b)
  rw [splitAwayAugmentation_algebraMap]
  change splitSectionQuotientEquiv ε
      (IsLocalization.Away.lift r (splitSectionQuotient_isUnit ε r hr)
        (algebraMap B (Localization.Away r) b)) = ε b
  rw [IsLocalization.Away.lift_eq, splitSectionQuotientEquiv_mk]

/-- The original residue lift and the extended section have the same actual kernel. -/
theorem splitAwayResidueMap_ker :
    RingHom.ker (splitAwayResidueMap ε r hr).toRingHom =
      RingHom.ker (splitAwayAugmentation ε r hr).toRingHom := by
  rw [← splitAwayResidueMap_comp]
  exact (RingHom.ker_comp_of_injective (splitAwayResidueMap ε r hr).toRingHom
    (splitSectionQuotientEquiv ε).injective).symm

/-- Principal localization along a split section preserves its original completion. -/
def splitAwayCompletionData :
    { e : AdicCompletion (RingHom.ker ε.toRingHom) B ≃ₐ[R]
      AdicCompletion (RingHom.ker (splitAwayAugmentation ε r hr).toRingHom)
        (Localization.Away r) //
      ∀ b : B, e (algebraMap B _ b) =
        algebraMap (Localization.Away r) _ (algebraMap B (Localization.Away r) b) } := by
  let : Algebra.FormallyEtale B (Localization.Away r) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  let c := Algebra.FormallyEtale.residueCompletionAlgEquiv
    (RingHom.ker ε.toRingHom) (splitAwayResidueMap ε r hr)
  let d := c.trans (AdicCompletion.idealCongrAlgEquiv B (splitAwayResidueMap_ker ε r hr))
  exact ⟨d.restrictScalars R, fun b => d.commutes b⟩

/-- The original section completion is unchanged by localization along the section. -/
def splitAwayCompletionAlgEquiv :
    AdicCompletion (RingHom.ker ε.toRingHom) B ≃ₐ[R]
      AdicCompletion (RingHom.ker (splitAwayAugmentation ε r hr).toRingHom)
        (Localization.Away r) :=
  (splitAwayCompletionData ε r hr).val

/-- The localization comparison retains the whole original scalar map. -/
theorem splitAwayCompletionAlgEquiv_algebraMap (b : B) :
    splitAwayCompletionAlgEquiv ε r hr (algebraMap B _ b) =
      algebraMap (Localization.Away r) _ (algebraMap B (Localization.Away r) b) :=
  (splitAwayCompletionData ε r hr).property b

end Away

universe u v

/-- A smooth algebra with a section over a local coefficient ring has its original
section-adic completion isomorphic to a finite-variable power-series ring.
The comparison retains every original polynomial coordinate, and the coefficient
ring is not assumed complete. -/
theorem exists_splitSectionCompletionAlgEquiv
    {R : Type u} {B : Type v} [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B] (ε : B →ₐ[R] R) :
    ∃ (ι : Type v) (_ : Finite ι) (x : ι → RingHom.ker ε.toRingHom)
      (e : MvPowerSeries ι R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B),
      ∀ p : MvPolynomial ι R, e (algebraMap _ (MvPowerSeries ι R) p) =
        algebraMap B _ (MvPolynomial.aeval (fun i => (x i).val) p) := by
  obtain ⟨r, hr, ι, hι, x, hx⟩ := exists_away_etale_split_coordinates ε
  let : Finite ι := hι
  let εr := splitAwayAugmentation ε r hr
  let xr : ι → RingHom.ker εr.toRingHom := fun i =>
    ⟨algebraMap B (Localization.Away r) (x i).val, by
      change splitAwayAugmentation ε r hr (algebraMap B (Localization.Away r) _) = 0
      rw [splitAwayAugmentation_algebraMap]
      exact (x i).property⟩
  have hxr : (splitCoordinateMap εr xr).toRingHom.FormallyEtale := by
    let :=  (splitCoordinateMap εr xr).toRingHom.toAlgebra
    let : Algebra.Etale (MvPolynomial ι R) (Localization.Away r) := hx
    exact inferInstanceAs (Algebra.FormallyEtale (MvPolynomial ι R) (Localization.Away r))
  let c := splitCoordinateCompletionAlgEquiv εr xr hxr
  let d := splitAwayCompletionAlgEquiv ε r hr
  refine ⟨ι, hι, x, c.trans d.symm, ?_⟩
  intro p
  apply d.injective
  change d (d.symm (c (algebraMap _ (MvPowerSeries ι R) p))) = _
  rw [AlgEquiv.apply_symm_apply]
  rw [show c (algebraMap _ (MvPowerSeries ι R) p) = _ from
    splitCoordinateCompletionAlgEquiv_polynomial εr xr hxr p]
  rw [splitAwayCompletionAlgEquiv_algebraMap]
  congr 1
  exact (MvPolynomial.comp_aeval_apply (fun i => (x i).val)
    (IsScalarTower.toAlgHom R B (Localization.Away r)) p).symm

/-- A small finite-variable presentation of the same original section completion.
The single coordinate witness is reindexed by the native finite-type equivalence. -/
theorem exists_fin_splitSectionCompletionAlgEquiv
    {R : Type u} {B : Type v} [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B] (ε : B →ₐ[R] R) :
    ∃ (n : ℕ) (x : Fin n → RingHom.ker ε.toRingHom)
      (e : MvPowerSeries (Fin n) R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B),
      ∀ p : MvPolynomial (Fin n) R, e (algebraMap _ (MvPowerSeries (Fin n) R) p) =
        algebraMap B _ (MvPolynomial.aeval (fun i => (x i).val) p) := by
  obtain ⟨ι, hι, x, e, he⟩ := exists_splitSectionCompletionAlgEquiv ε
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let k := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i => x (k i), (MvPowerSeries.renameEquiv R k).trans e, ?_⟩
  intro p
  change e (MvPowerSeries.rename k (p : MvPowerSeries (Fin (Fintype.card ι)) R)) = _
  rw [MvPowerSeries.rename_coe]
  exact (he (MvPolynomial.rename k p)).trans
    (congrArg (algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B))
      (MvPolynomial.aeval_rename k (fun i => (x i).val) p))

end Algebra.Smooth
