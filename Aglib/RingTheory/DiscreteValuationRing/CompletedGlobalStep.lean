/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalSource
public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalInjection
public import Aglib.RingTheory.DiscreteValuationRing.CompletedPowerSeriesResidueSeparable
public import Aglib.RingTheory.DiscreteValuationRing.CompletedGenericSource
public import Aglib.RingTheory.NeronModification.GlobalPoint
public import Aglib.RingTheory.NeronModification.FractionPointSquare
public import Aglib.RingTheory.NeronModification.GeneralCentreStep
public import Aglib.RingTheory.NeronModification.EvaluatedFittingLocalization
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# The actual global Néron step under the completed-fraction condition

The finite-type source is an algebra over the ORIGINAL polynomial ring and is
embedded in the ORIGINAL completed power-series ring. Only the proof of strict
improvement localizes this source and the coefficient ring. Both evaluated
Fitting ideals are then transported back through the SAME modification map.
The old common fraction field, its original polynomial action, and its fixed
embedding in the target fraction field are retained.
-/

@[expose] public noncomputable section

open IsLocalRing
open Algebra.NeronModification ParameterLocalization.SourceCentre

namespace PowerSeriesLocalization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type*) [Finite ι] (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial ι R
local notation "C" => MvPowerSeries ι Rhat
local notation "A" => ParameterLocalization.Ring R ι p
local notation "S" => CompletedRing R ι p
local notation "qC" => coefficientIdeal Rhat ι (algebraMap R Rhat p)

local instance : IsDomain C := NoZeroDivisors.to_isDomain _
local instance : Fact (Irreducible (algebraMap R Rhat p)) :=
  ⟨AdicCompletion.irreducible_algebraMap R p (Fact.out : Irreducible p)⟩
/-- The original polynomial coefficients act on the same completed-series target
through `completedPolynomialInclusion`. -/
local instance completedInclusionAlgebra : Algebra P C :=
  (completedPolynomialInclusion R ι).toAlgebra

variable {B : Type*} [CommRing B] [Algebra (MvPolynomial ι R) B]
  [Algebra.FiniteType (MvPolynomial ι R) B]
variable (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
  [Algebra (MvPolynomial ι R) K] [IsScalarTower (MvPolynomial ι R) B K]
  [Algebra (FractionRing (MvPolynomial ι R)) K]
  [IsScalarTower (MvPolynomial ι R) (FractionRing (MvPolynomial ι R)) K]
variable {ν : Type*} [Finite ν] (g : ν → B)

local notation "M" => Modification (algebraMap P B (MvPolynomial.C p)) g

/-- One genuine global step, with the original finite centre generators and
fixed common field. The intrinsic completed-fraction condition supplies generic
separability; residual separability is that of the actual completed-power-series
pair. Strictness is in the fixed localized target, not in the global power-series
ring. -/
theorem exists_completedGlobalStep_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    (f : B →ₐ[P] C) (hinj : Function.Injective f)
    (j : K →+* FractionRing C)
    (hj : j.comp (algebraMap B K) = (algebraMap C (FractionRing C)).comp f.toRingHom)
    (r : ℕ) (hr : Algebra.trdeg (FractionRing P) K = (r : Cardinal))
    (hgen : Ideal.span (Set.range g) = residueCentre (MvPolynomial.C p) f)
    (hproper : (Module.fittingIdeal B (KaehlerDifferential P B) r).map
      ((algebraMap C S).comp f.toRingHom) ≠ ⊤) :
    ∃ (fM : M →ₐ[P] C) (kM : M →+* K),
      (∀ b, fM (of (algebraMap P B (MvPolynomial.C p)) g b) = f b) ∧
      Function.Injective fM ∧ IsDomain M ∧ Algebra.FiniteType P M ∧
      (∀ b, kM (of (algebraMap P B (MvPolynomial.C p)) g b) = algebraMap B K b) ∧
      (letI : Algebra M K := kM.toAlgebra
       IsFractionRing M K ∧ IsScalarTower P M K) ∧
      j.comp kM = (algebraMap C (FractionRing C)).comp fM.toRingHom ∧
      (Module.fittingIdeal B (KaehlerDifferential P B) r).map
          ((algebraMap C S).comp f.toRingHom) <
        (Module.fittingIdeal M (KaehlerDifferential P M) r).map
          ((algebraMap C S).comp fM.toRingHom) := by
  classical
  let : IsDomain B := Function.Injective.isDomain f hinj
  let : IsDiscreteValuationRing A := ParameterLocalization.isDiscreteValuationRing R ι p
  let : IsDiscreteValuationRing S := completedRing_isDiscreteValuationRing R ι p
  let : Algebra A S := (completedPolynomialMap R ι p).toAlgebra
  let : IsLocalHom (algebraMap A S) := completedPolynomialMap_isLocalHom R ι p
  have hresidueAlgebra :
      (completedPolynomialResidueMap R ι p).toAlgebra =
        (inferInstance : Algebra (ResidueField A) (ResidueField S)) := by
    apply Algebra.algebra_ext
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective (R := A) x
    change completedPolynomialResidueMap R ι p (residue A a) =
      algebraMap (ResidueField A) (ResidueField S) (residue A a)
    rw [completedPolynomialResidueMap, ResidueField.map_residue,
      ResidueField.algebraMap_residue]
    rfl
  let T (a : Algebra (ResidueField A) (ResidueField S)) : Prop :=
    letI := a
    Algebra.IsTranscendentalSeparable (ResidueField A) (ResidueField S)
  have ht : T (completedPolynomialResidueMap R ι p).toAlgebra :=
    isTranscendentalSeparable_completedPolynomialResidueMap R ι p
  let : Algebra.IsTranscendentalSeparable (ResidueField A) (ResidueField S) :=
    Eq.mp (congrArg T hresidueAlgebra) ht
  let D := GlobalLocalSource R ι p (B := B)
  let Q := (ParameterLocalization.parameterIdeal R ι p).primeCompl
  let : IsLocalization (Algebra.algebraMapSubmonoid B Q) D :=
    inferInstanceAs (IsLocalization (globalSourceDenominators R ι p (B := B))
      (GlobalLocalSource R ι p (B := B)))
  let pB : B := algebraMap P B (MvPolynomial.C p)
  let pA : A := algebraMap R A p
  let gD : ν → D := fun i => algebraMap B D (g i)
  let ρ : C →+* S := algebraMap C S
  let χ₀ : B →+* S := ρ.comp f.toRingHom
  have hf : f.toRingHom.comp (algebraMap P B) = completedPolynomialInclusion R ι := by
    apply RingHom.ext
    intro a
    exact f.commutes a
  let χring : D →+* S := globalLocalizedPoint R ι p f.toRingHom hf
  have hχB (b : B) : χring (algebraMap B D b) = ρ (f b) :=
    localizedPointAtPrime_algebraMap
      (globalSourceDenominators R ι p (B := B)) qC f.toRingHom
      (globalSourceDenominators_le_comap R ι p f.toRingHom hf) b
  have hχA : χring.comp (algebraMap A D) = algebraMap A S := by
    apply IsLocalization.ringHom_ext Q
    apply RingHom.ext
    intro a
    change χring (algebraMap A D (algebraMap P A a)) =
      completedPolynomialMap R ι p (algebraMap P A a)
    rw [← IsScalarTower.algebraMap_apply P A D,
      IsScalarTower.algebraMap_apply P B D, hχB, f.commutes]
    exact (completedPolynomialMap_polynomial R ι p a).symm
  let χ : D →ₐ[A] S :=
    { __ := χring
      commutes' := fun a => DFunLike.congr_fun hχA a }
  let : IsDomain D := globalLocalSource_isDomain R ι p f.toRingHom hf hinj
  let : Algebra.FiniteType A D := globalLocalSource_finiteType R ι p B
  have hχinj : Function.Injective χ :=
    globalLocalizedPoint_injective R ι p f.toRingHom hf hinj
  let : Fact (Irreducible pA) := ⟨ParameterLocalization.uniformizer_irreducible R ι p⟩
  have hpS : Irreducible (algebraMap A S pA) := by
    change Irreducible (completedPolynomialMap R ι p (algebraMap R A p))
    rw [completedPolynomialMap_uniformizer]
    exact uniformizer_irreducible Rhat ι (algebraMap R Rhat p)
  have hscalar : algebraMap A D pA = algebraMap B D pB := by
    change algebraMap A D (algebraMap R A p) =
      algebraMap B D (algebraMap P B (MvPolynomial.C p))
    rw [← IsScalarTower.algebraMap_apply P B D]
    change algebraMap A D (algebraMap R A p) =
      algebraMap P D (algebraMap R P p)
    rw [IsScalarTower.algebraMap_apply P A D, ← IsScalarTower.algebraMap_apply R P A]
  have hCscalar : algebraMap P C (MvPolynomial.C p) =
      MvPowerSeries.C (algebraMap R Rhat p) := by
    change completedPolynomialInclusion R ι (MvPolynomial.C p) = _
    simp [completedPolynomialInclusion]
  have hpC : algebraMap P C (MvPolynomial.C p) ≠ 0 := by
    rw [hCscalar]
    exact fun h => (Fact.out : Irreducible (algebraMap R Rhat p)).ne_zero
      (MvPowerSeries.C_injective (by simpa using h))
  have hpB : pB ≠ 0 := by
    intro h
    apply hpC
    rw [← f.commutes]
    change f pB = 0
    rw [h, map_zero]
  have hqC : qC = Ideal.span {algebraMap P C (MvPolynomial.C p)} := by
    rw [hCscalar]
    rfl
  have hcentre : centre χ =
      (residueCentre (MvPolynomial.C p) f).map (algebraMap B D) := by
    have hker : centre χ = RingHom.ker ((residue S).comp χring) := by
      ext b
      exact (residue_eq_zero_iff (χring b)).symm
    rw [hker]
    change RingHom.ker ((residue S).comp
      (globalLocalizedPoint R ι p f.toRingHom hf)) = _
    rw [ker_residue_globalLocalizedPoint, hqC]
    rfl
  have hgenD : Ideal.span (insert (algebraMap A D pA) (Set.range gD)) = centre χ := by
    calc
      _ = (Ideal.span (insert pB (Set.range g))).map (algebraMap B D) := by
        rw [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, hscalar]
        rfl
      _ = (residueCentre (MvPolynomial.C p) f).map (algebraMap B D) := by
        rw [span_insert_scalar_eq_residueCentre (MvPolynomial.C p) f g hgen]
      _ = centre χ := hcentre.symm
  have hg (i : ν) : g i ∈ residueCentre (MvPolynomial.C p) f := by
    rw [← hgen]
    exact Ideal.subset_span ⟨i, rfl⟩
  let hpreg : IsRegular (algebraMap P C (MvPolynomial.C p)) :=
    isRegular_iff_ne_zero.mpr hpC
  let fM : M →ₐ[P] C := residueLift (MvPolynomial.C p) f g hg hpreg
  let χM : M →+* S := ρ.comp fM.toRingHom
  let : Algebra.FiniteType P M := finiteType_modification pB g
  have hχM : χM.comp (of pB g) = χ₀ := by
    ext b
    change ρ (fM (of pB g b)) = ρ (f b)
    rw [residueLift_of]
  have hpoint : χ.toRingHom.comp (algebraMap B D) = (RingHom.id S).comp χ₀ := by
    ext b
    exact hχB b
  have hold : (Module.fittingIdeal D (KaehlerDifferential A D) r).map χ.toRingHom =
      (Module.fittingIdeal B (KaehlerDifferential P B) r).map χ₀ := by
    simpa only [Ideal.map_id] using
      KaehlerDifferential.map_fittingIdeal_of_isLocalizationSquare P A B D Q
        χ₀ χ.toRingHom (RingHom.id S) hpoint r
  have hproperD : (Module.fittingIdeal D (KaehlerDifferential A D) r).map χ.toRingHom ≠ ⊤ := by
    rw [hold]
    exact hproper
  -- All generic actions here are the canonical actions expected by the local
  -- theorem. No fraction-polynomial action is put on the global source B.
  let : FaithfulSMul A D :=
    ParameterLocalization.faithfulSMul_source_of_map_irreducible pA χ hpS
  let : Algebra (FractionRing A) (FractionRing D) :=
    FractionRing.liftAlgebra A (FractionRing D)
  let : IsScalarTower A (FractionRing A) (FractionRing D) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing D)
  let : Algebra.EssFiniteType A (FractionRing D) :=
    Algebra.EssFiniteType.comp A D (FractionRing D)
  let : Algebra.EssFiniteType (FractionRing A) (FractionRing D) :=
    Algebra.EssFiniteType.of_comp A (FractionRing A) (FractionRing D)
  have hgeneric : Algebra.IsSeparablyGenerated (FractionRing A) (FractionRing D) :=
    isSeparablyGenerated_completedLocalizedSource R ι p hcoeff χ hχinj
  -- Algebraic localization towers compare the original generic degree with
  -- that of this literal localized source, including different universes.
  let : FaithfulSMul P D := (faithfulSMul_iff_algebraMap_injective P D).mpr (by
    rw [IsScalarTower.algebraMap_eq P A D]
    exact (FaithfulSMul.algebraMap_injective A D).comp
      (IsLocalization.injective A
        (Ideal.primeCompl_le_nonZeroDivisors (ParameterLocalization.parameterIdeal R ι p))))
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr (by
    intro a b h
    apply FaithfulSMul.algebraMap_injective P D
    rw [IsScalarTower.algebraMap_apply P B D,
      IsScalarTower.algebraMap_apply P B D, h])
  let : FaithfulSMul B D := (faithfulSMul_iff_algebraMap_injective B D).mpr (by
    intro a b h
    apply hinj
    apply IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors qC)
    change ρ (f a) = ρ (f b)
    rw [← hχB a, ← hχB b, h])
  let : Algebra.IsAlgebraic P A := IsLocalization.isAlgebraic A Q
  let : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  let : Algebra.IsAlgebraic P (FractionRing P) :=
    IsLocalization.isAlgebraic (FractionRing P) (nonZeroDivisors P)
  let : Algebra.IsAlgebraic B D :=
    IsLocalization.isAlgebraic D (globalSourceDenominators R ι p (B := B))
  let : Algebra.IsAlgebraic D (FractionRing D) :=
    IsLocalization.isAlgebraic (FractionRing D) (nonZeroDivisors D)
  let : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  have hPK : Algebra.trdeg P K = (r : Cardinal) := by
    have h := lift_trdeg_add_eq P (FractionRing P) K
    have h' : Algebra.trdeg (FractionRing P) K = Algebra.trdeg P K := by
      simpa only [trdeg_eq_zero, Cardinal.lift_zero, zero_add, Cardinal.lift_inj] using h
    exact h'.symm.trans hr
  have hPB : Algebra.trdeg P B = (r : Cardinal) := by
    have h := lift_trdeg_add_eq P B K
    apply Cardinal.lift_injective
    simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero, hPK,
      Cardinal.lift_natCast] using h
  have hPD : Algebra.trdeg P D = (r : Cardinal) := by
    have h := trdeg_add_eq P B («A» := D)
    simpa only [trdeg_eq_zero, add_zero, hPB] using h.symm
  have hPFD : Algebra.trdeg P (FractionRing D) = (r : Cardinal) := by
    have h := trdeg_add_eq P D («A» := FractionRing D)
    simpa only [trdeg_eq_zero, add_zero, hPD] using h.symm
  have hAFD : Algebra.trdeg A (FractionRing D) = (r : Cardinal) := by
    have h := lift_trdeg_add_eq P A (FractionRing D)
    apply Cardinal.lift_injective
    simpa only [trdeg_eq_zero, Cardinal.lift_zero, zero_add, hPFD,
      Cardinal.lift_natCast] using h
  have hrD : Algebra.trdeg (FractionRing A) (FractionRing D) = (r : Cardinal) := by
    have h := lift_trdeg_add_eq A (FractionRing A) (FractionRing D)
    apply Cardinal.lift_injective
    simpa only [trdeg_eq_zero, Cardinal.lift_zero, zero_add, hAFD,
      Cardinal.lift_natCast] using h
  obtain ⟨n, ⟨P₀⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    (inferInstance : Algebra.FiniteType A D)
  let z : ν → S := fun i => ρ (residueDivision (MvPolynomial.C p) f g hg i)
  have hz (i : ν) : χ (algebraMap A D pA) * z i = χ (gD i) := by
    rw [hscalar]
    change χring (algebraMap B D pB) *
      ρ (residueDivision (MvPolynomial.C p) f g hg i) = χring (algebraMap B D (g i))
    rw [hχB, hχB, ← map_mul, scalar_mul_residueDivision]
  have hpχ : IsRegular (χ (algebraMap A D pA)) := by
    rw [χ.commutes]
    exact isRegular_iff_ne_zero.mpr hpS.ne_zero
  let ψ := lift (algebraMap A D pA) gD χ.toRingHom z hz hpχ
  have hψ : ψ.comp (of (algebraMap A D pA) gD) = χ.toRingHom := by
    ext b
    exact lift_of _ _ _ _ hz hpχ b
  have hstrict := fittingIdeal_lt_of_generalCentre pA χ hχinj hpS hgeneric
    r hrD P₀ gD hgenD hproperD ψ hψ
  -- Change only the syntactic name of the same localized scalar, so the
  -- transport theorem uses literally baseChangeOriginal for the SAME g.
  have hex : ∃ χN : Modification (algebraMap B D pB) gD →+* S,
      χN.comp (of (algebraMap B D pB) gD) = χ.toRingHom ∧
      (Module.fittingIdeal D (KaehlerDifferential A D) r).map χ.toRingHom <
        (Module.fittingIdeal (Modification (algebraMap B D pB) gD)
          (KaehlerDifferential A (Modification (algebraMap B D pB) gD)) r).map χN := by
    rw [← hscalar]
    exact ⟨ψ, hψ, hstrict⟩
  obtain ⟨χN, hχN, hstrictN⟩ := hex
  have hpχ₀ : IsRegular ((RingHom.id S) (χ₀ pB)) := by
    change IsRegular (ρ (f pB))
    rw [← hχB pB, ← hscalar]
    exact hpχ
  have hnew := map_fittingIdeal_baseChangeOriginal_of_isLocalizationSquare
    (R := P) (R' := A) (B' := D) pB g Q χ₀ χ.toRingHom (RingHom.id S)
    hpoint χM χN hχM hχN hpχ₀ r
  simp only [Ideal.map_id] at hnew
  rw [hold, hnew] at hstrictN
  refine ⟨fM, fractionPoint K pB g hpB, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_, hstrictN⟩
  · intro b
    exact residueLift_of (MvPolynomial.C p) f g hg hpreg b
  · exact residueLift_injective (MvPolynomial.C p) f hinj g hg hpreg
  · exact residueLift_isDomain (MvPolynomial.C p) f hinj g hg hpreg
  · intro b
    exact fractionPoint_of K pB g hpB b
  · exact ⟨isFractionRing_fractionPoint K pB g hpB,
      fractionPoint_scalarTower K pB g hpB⟩
  · exact fractionPoint_square K (FractionRing C) pB g hpB f.toRingHom
      (residueDivision (MvPolynomial.C p) f g hg)
      (scalar_mul_residueDivision (MvPolynomial.C p) f g hg)
      (by
        change IsRegular (f (algebraMap P B (MvPolynomial.C p)))
        rw [f.commutes]
        exact hpreg) j (algebraMap C (FractionRing C)) hj

variable [CharZero R]

/-- Characteristic zero supplies the intrinsic completed-fraction condition
for the same actual global construction. -/
theorem exists_completedGlobalStep_of_charZero
    (f : B →ₐ[P] C) (hinj : Function.Injective f)
    (j : K →+* FractionRing C)
    (hj : j.comp (algebraMap B K) = (algebraMap C (FractionRing C)).comp f.toRingHom)
    (r : ℕ) (hr : Algebra.trdeg (FractionRing P) K = (r : Cardinal))
    (hgen : Ideal.span (Set.range g) = residueCentre (MvPolynomial.C p) f)
    (hproper : (Module.fittingIdeal B (KaehlerDifferential P B) r).map
      ((algebraMap C S).comp f.toRingHom) ≠ ⊤) :
    ∃ (fM : M →ₐ[P] C) (kM : M →+* K),
      (∀ b, fM (of (algebraMap P B (MvPolynomial.C p)) g b) = f b) ∧
      Function.Injective fM ∧ IsDomain M ∧ Algebra.FiniteType P M ∧
      (∀ b, kM (of (algebraMap P B (MvPolynomial.C p)) g b) = algebraMap B K b) ∧
      (letI : Algebra M K := kM.toAlgebra
       IsFractionRing M K ∧ IsScalarTower P M K) ∧
      j.comp kM = (algebraMap C (FractionRing C)).comp fM.toRingHom ∧
      (Module.fittingIdeal B (KaehlerDifferential P B) r).map
          ((algebraMap C S).comp f.toRingHom) <
        (Module.fittingIdeal M (KaehlerDifferential P M) r).map
          ((algebraMap C S).comp fM.toRingHom) := by
  exact exists_completedGlobalStep_of_geometricallyReducedFractionCompletion R ι p K g
    (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R)
    f hinj j hj r hr hgen hproper

end PowerSeriesLocalization
