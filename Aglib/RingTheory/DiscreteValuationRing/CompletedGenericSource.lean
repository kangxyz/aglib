/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.EmbeddedField
public import Aglib.RingTheory.AdicCompletion.GeometricallyReducedFraction
public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalCentre
public import Aglib.RingTheory.MvPowerSeries.GenericDomainSeparable

/-!
# Generic separating generation of the actual localized finite source

The ambient field is the fraction field of the original completed power-series
ring. The localized target maps into this field by its literal localization
lift. No completion of the polynomial coefficient-prime localization is used.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w

namespace PowerSeriesLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial ι R
local notation "C" => MvPowerSeries ι Rhat
local notation "A" => ParameterLocalization.Ring R ι p
local notation "S" => CompletedRing R ι p
local notation "qC" => coefficientIdeal Rhat ι (algebraMap R Rhat p)

local instance completedGenericSourceDomain : IsDomain C := NoZeroDivisors.to_isDomain _
local instance completedGenericSourceUniformizer :
    Fact (Irreducible (algebraMap R Rhat p)) :=
  ⟨AdicCompletion.irreducible_algebraMap R p (Fact.out : Irreducible p)⟩
/-- The parameter DVR acts on the original localized completed-series ring
through `completedPolynomialMap`. -/
local instance completedTargetAlgebra : Algebra A S :=
  (completedPolynomialMap R ι p).toAlgebra

omit [Finite ι] in
/-- Both definitions are the actual coefficientwise polynomial inclusion. -/
lemma polynomialCoefficientMap_eq_completedPolynomialInclusion :
    MvPowerSeries.polynomialCoefficientMap (σ := ι) (algebraMap R Rhat) =
      completedPolynomialInclusion R ι := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [MvPowerSeries.polynomialCoefficientMap, completedPolynomialInclusion]
  · intro i
    simp [MvPowerSeries.polynomialCoefficientMap, completedPolynomialInclusion]

/-- An actual finite-type source embedded in the actual localized completed-series
ring has a separably generated fraction field over the actual localized
polynomial base. Its fraction-field action is exactly `FractionRing.liftAlgebra`.
The source universe is independent of the coefficient and parameter universes. -/
theorem isSeparablyGenerated_completedLocalizedSource
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    {D : Type w} [CommRing D] [IsDomain D] [Algebra A D]
    [FaithfulSMul A D] [Algebra.FiniteType A D]
    (χ : D →ₐ[A] S) (hχ : Function.Injective χ) :
    let := FractionRing.liftAlgebra A (FractionRing D)
    Algebra.IsSeparablyGenerated (FractionRing A) (FractionRing D) := by
  classical
  let : FaithfulSMul R Rhat := AdicCompletion.faithfulSMul_maximalIdeal R
  let : Algebra (FractionRing R) (FractionRing Rhat) :=
    FractionRing.liftAlgebra R (FractionRing Rhat)
  have hgeo : Algebra.IsGeometricallyReduced (FractionRing R) (FractionRing Rhat) :=
    hcoeff
  let F := FractionRing P
  let E := FractionRing D
  let L := FractionRing C
  let Q := (ParameterLocalization.parameterIdeal R ι p).primeCompl
  let N := (qC).primeCompl
  have hQ : Q ≤ nonZeroDivisors P :=
    Ideal.primeCompl_le_nonZeroDivisors (ParameterLocalization.parameterIdeal R ι p)
  have hN : N ≤ nonZeroDivisors C := Ideal.primeCompl_le_nonZeroDivisors qC
  -- The two maps out of the actual localizations, including their native towers.
  let : Algebra A F := IsLocalization.originalFractionAlgebra P A Q hQ
  let e : FractionRing A ≃ₐ[A] F := IsLocalization.originalFractionEquiv P A Q hQ
  let : Algebra S L := IsLocalization.originalFractionAlgebra C S N hN
  let : IsFractionRing S L := IsLocalization.isFractionRing_originalFractionAlgebra C S N hN
  let c : S →+* L := IsLocalization.toOriginalFractionRing C S N hN
  have hc (s : C) : c (algebraMap C S s) = algebraMap C L s :=
    IsLocalization.toOriginalFractionRing_algebraMap C S N hN s
  have hcinj : Function.Injective c := IsFractionRing.injective S L
  -- The real source fraction embedding, not an assumed ambient identification.
  let d : E →+* L := IsFractionRing.lift («A» := D) (K := E) (g := c.comp χ.toRingHom)
    (hcinj.comp hχ)
  have hd (x : D) : d (algebraMap D E x) = c (χ x) :=
    IsFractionRing.lift_algebraMap («A» := D) (K := E)
      (g := c.comp χ.toRingHom) (hcinj.comp hχ) x
  let a : F →+* L := MvPowerSeries.polynomialSeriesFractionMap
    (σ := ι) (algebraMap R Rhat) (FaithfulSMul.algebraMap_injective R Rhat)
  have ha (q : P) : a (algebraMap P F q) =
      algebraMap C L (completedPolynomialInclusion R ι q) := by
    rw [show a = MvPowerSeries.polynomialSeriesFractionMap
      (σ := ι) (algebraMap R Rhat) (FaithfulSMul.algebraMap_injective R Rhat) from rfl,
      MvPowerSeries.polynomialSeriesFractionMap_algebraMap,
      polynomialCoefficientMap_eq_completedPolynomialInclusion]
  let : Algebra F L := a.toAlgebra
  let : Algebra.IsTranscendentalSeparable F L :=
    MvPowerSeries.isTranscendentalSeparable_domainFractionRing R Rhat ι hgeo
  -- Transport only the coefficient field, along the proved fraction equivalence.
  let b : FractionRing A →+* L := a.comp e.toRingHom
  let : Algebra (FractionRing A) L := b.toAlgebra
  have he : b.comp e.symm.toRingHom = a := by
    apply RingHom.ext
    intro x
    exact congrArg a (e.apply_symm_apply x)
  let : Algebra.IsTranscendentalSeparable (FractionRing A) L :=
    Algebra.isTranscendentalSeparable_of_baseRingEquiv e.symm.toRingEquiv he
  -- The source action remains precisely the one required by GeneralCentreStep.
  let : Algebra (FractionRing A) E := FractionRing.liftAlgebra A E
  let : IsScalarTower A (FractionRing A) E := FractionRing.isScalarTower_liftAlgebra A E
  have hbase : d.comp (algebraMap A E) = b.comp (algebraMap A (FractionRing A)) := by
    apply IsLocalization.ringHom_ext Q
    apply RingHom.ext
    intro q
    change d (algebraMap A E (algebraMap P A q)) =
      a (e (algebraMap A (FractionRing A) (algebraMap P A q)))
    rw [IsScalarTower.algebraMap_apply A D E, hd, χ.commutes, e.commutes]
    change c (completedPolynomialMap R ι p (algebraMap P A q)) =
      a (IsLocalization.toOriginalFractionRing P A Q hQ (algebraMap P A q))
    rw [completedPolynomialMap_polynomial, hc,
      IsLocalization.toOriginalFractionRing_algebraMap, ha]
    rfl
  have hsquare : d.comp (algebraMap (FractionRing A) E) = b := by
    apply IsFractionRing.ringHom_ext («A» := A)
    intro x
    change d (algebraMap (FractionRing A) E (algebraMap A (FractionRing A) x)) = b _
    rw [← IsScalarTower.algebraMap_apply A (FractionRing A) E]
    exact RingHom.congr_fun hbase x
  let da : E →ₐ[FractionRing A] L :=
    { d with commutes' := fun x => RingHom.congr_fun hsquare x }
  let : Algebra.EssFiniteType A E := Algebra.EssFiniteType.comp A D E
  let : Algebra.EssFiniteType (FractionRing A) E :=
    Algebra.EssFiniteType.of_comp A (FractionRing A) E
  exact Algebra.isSeparablyGenerated_of_algHom da

end PowerSeriesLocalization
