/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.CrossFieldFractionSeparable
public import Aglib.RingTheory.MvPowerSeries.FractionCoefficientMap
public import Aglib.RingTheory.Localization.OriginalFraction
public import Aglib.FieldTheory.SeparablyGenerated.Restriction
public import Aglib.FieldTheory.SeparablyGenerated.Equivalence

/-!
# The canonical generic polynomial-to-series extension of domains

The only geometric hypothesis concerns the actual coefficient fraction fields.
No excellence theorem or completion property is asserted here.
-/

@[expose] public noncomputable section

namespace MvPowerSeries

/-- Polynomial inclusion followed by the specified coefficient map. -/
def polynomialCoefficientMap {R S σ : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : MvPolynomial σ R →+* MvPowerSeries σ S :=
  (MvPowerSeries.map f).comp MvPolynomial.coeToMvPowerSeries.ringHom

lemma polynomialCoefficientMap_injective {R S σ : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (polynomialCoefficientMap (σ := σ) f) :=
  (coefficientMap_injective f hf).comp (MvPolynomial.coe_injective σ R)

/-- The actual generic map is the unique fraction lift of polynomial inclusion. -/
def polynomialSeriesFractionMap {R S σ : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) :
    FractionRing (MvPolynomial σ R) →+* FractionRing (MvPowerSeries σ S) :=
  IsFractionRing.lift (K := FractionRing (MvPolynomial σ R))
    (g := (algebraMap (MvPowerSeries σ S) (FractionRing (MvPowerSeries σ S))).comp
      (polynomialCoefficientMap f))
    ((IsFractionRing.injective (MvPowerSeries σ S) (FractionRing (MvPowerSeries σ S))).comp
      (polynomialCoefficientMap_injective f hf))

@[simp]
lemma polynomialSeriesFractionMap_algebraMap {R S σ : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Injective f) (q : MvPolynomial σ R) :
    polynomialSeriesFractionMap f hf (algebraMap _ (FractionRing (MvPolynomial σ R)) q) =
      algebraMap _ (FractionRing (MvPowerSeries σ S)) (polynomialCoefficientMap f q) := by
  unfold polynomialSeriesFractionMap
  exact IsFractionRing.lift_algebraMap _ q

/-- The specified polynomial-series fraction map gives the genuine native tower. -/
lemma polynomialSeriesFractionMap_tower (k L σ : Type*) [Field k] [Field L] [Algebra k L] :
    let := (polynomialSeriesFractionMap (σ := σ) (algebraMap k L)
      (RingHom.injective (algebraMap k L))).toAlgebra
    IsScalarTower (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ L)) := by
  let := (polynomialSeriesFractionMap (σ := σ) (algebraMap k L)
    (RingHom.injective (algebraMap k L))).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro q
  rw [show algebraMap (FractionRing (MvPolynomial σ k))
      (FractionRing (MvPowerSeries σ L)) =
      polynomialSeriesFractionMap (σ := σ) (algebraMap k L)
        (RingHom.injective (algebraMap k L)) from rfl]
  rw [polynomialSeriesFractionMap_algebraMap]
  rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k) (MvPowerSeries σ L)
    (FractionRing (MvPowerSeries σ L))]
  rfl

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The actual domain extension is generally separable whenever its coefficient
fraction-field extension is geometrically reduced. The coefficient action and
polynomial-series action are both canonical fraction lifts. -/
theorem isTranscendentalSeparable_domainFractionRing
    (R S σ : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] :
    let := FractionRing.liftAlgebra R (FractionRing S)
    let := (polynomialSeriesFractionMap (σ := σ) (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S)).toAlgebra
    Algebra.IsGeometricallyReduced (FractionRing R) (FractionRing S) →
      Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial σ R))
        (FractionRing (MvPowerSeries σ S)) := by
  classical
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let P := MvPolynomial σ R
  let Q := MvPolynomial σ K
  let T := MvPowerSeries σ S
  let U := MvPowerSeries σ L
  let F := FractionRing P
  let B := FractionRing Q
  let E := FractionRing T
  let D := FractionRing U
  let a : F →+* E := polynomialSeriesFractionMap (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S)
  let : Algebra F E := a.toAlgebra
  change Algebra.IsGeometricallyReduced K L → Algebra.IsTranscendentalSeparable F E
  intro hgeo
  let : Algebra.IsGeometricallyReduced K L := hgeo
  let b : B →+* D := polynomialSeriesFractionMap (algebraMap K L)
    (RingHom.injective (algebraMap K L))
  let : Algebra B D := b.toAlgebra
  let : IsScalarTower Q B D := polynomialSeriesFractionMap_tower K L σ
  let : Algebra.IsTranscendentalSeparable B D :=
    isTranscendentalSeparable_crossFractionRing_of_tower K L σ
  let j : E →+* D := fractionToCoefficientFraction S σ
  let M := (nonZeroDivisors R).map (MvPolynomial.C (σ := σ))
  let hM : M ≤ nonZeroDivisors P := MvPolynomial.coefficient_nonZeroDivisors_le R σ
  let : Algebra Q F := IsLocalization.originalFractionAlgebra P Q M hM
  let e : B ≃ₐ[Q] F := IsLocalization.originalFractionEquiv P Q M hM
  have hcoeff (r : R) : algebraMap K L (algebraMap R K r) =
      algebraMap S L (algebraMap R S r) := by
    rw [← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R S L]
  have ha (q : P) : a (algebraMap P F q) =
      algebraMap T E (polynomialCoefficientMap (algebraMap R S) q) :=
    polynomialSeriesFractionMap_algebraMap _ _ q
  have hb (q : Q) : b (algebraMap Q B q) =
      algebraMap U D (polynomialCoefficientMap (algebraMap K L) q) :=
    polynomialSeriesFractionMap_algebraMap _ _ q
  have hj (t : T) : j (algebraMap T E t) =
      algebraMap U D (MvPowerSeries.map (algebraMap S L) t) :=
    fractionCoefficientMap_algebraMap _ _ t
  have hPC (r : R) : algebraMap P Q (MvPolynomial.C r) =
      MvPolynomial.C (algebraMap R K r) := MvPolynomial.map_C (algebraMap R K) r
  have hPX (i : σ) : algebraMap P Q (MvPolynomial.X i) = MvPolynomial.X i :=
    MvPolynomial.map_X (algebraMap R K) i
  have hpoly : ((j.comp a).comp (algebraMap P F)) =
      (b.comp (algebraMap Q B)).comp (algebraMap P Q) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, ha, hb, hj, hPC,
        polynomialCoefficientMap,
        MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C,
        MvPowerSeries.map_C, hcoeff]
    · intro i
      simp only [RingHom.comp_apply, ha, hb, hj, hPX,
        polynomialCoefficientMap,
        MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X,
        MvPowerSeries.map_X]
  have hsquare : (j.comp a).comp e.toRingHom = b :=
    IsLocalization.originalFractionEquiv_comp_eq P Q M hM (j.comp a) b
      (fun q => RingHom.congr_fun hpoly q)
  let : Algebra F D := (j.comp a).toAlgebra
  let : Algebra.IsTranscendentalSeparable F D :=
    Algebra.isTranscendentalSeparable_of_baseRingEquiv e.toRingEquiv hsquare
  let ja : E →ₐ[F] D := { j with commutes' := fun x => rfl }
  exact Algebra.isTranscendentalSeparable_of_algHom ja

end MvPowerSeries
