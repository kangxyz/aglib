/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.LocalTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.KummerPreimage

/-! # Original Kummer classes on the actual torsion-parameter family

The literal underlying bounded line bundle is pulled to the actual reduced
power locus and then to actual chart opens. Canonical power-pullback maps
convert the accepted local power trivialization into an original H1(mu_n)
class with that literal Picard image. Its original geometric restrictions
retain the same line bundle. No uniqueness, finiteness, or proper-base-change
identification is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

attribute [local instance] hasSheafifyLarge HasExt.standard

universe u w

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

/-- The literal underlying bounded line bundle on the actual reduced power locus. -/
def locusLineBundle (g n : ℕ) : LineBundle (powerLocusCurve X o ho g n) :=
  pullbackLineBundle (Hom.familyMap X.hom (parameter X.hom g).hom
    (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)
    (powerNonvanishingι X.hom o ho g n) rfl) (lineBundle X.hom o ho g)

/-- The restricted power coefficient is canonically the power of the literal
restricted underlying bundle, through the original module pullback map. -/
def locusLineBundlePowerIso (g n : ℕ) :
    (powerLocusLineBundle X o ho g n).val ≅
      (tensorPowerLineBundle _ (locusLineBundle X o ho g n) n).val :=
  PowerPullback.pullbackPowerIso (Hom.familyMap X.hom (parameter X.hom g).hom
    (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)
    (powerNonvanishingι X.hom o ho g n) rfl) (lineBundle X.hom o ho g) n

section AffineChart

variable {R : Type u} [CommRing R] (g n : ℕ)
  (j : Spec (.of R) ⟶ powerNonvanishingLocus X.hom o ho g n)

/-- The literal underlying bundle on the actual inverse image of a chart open. -/
def locusChartOpenLineBundle (U : (Spec (.of R)).Opens) :
    LineBundle ((pullback.snd (powerLocusProjection X o ho g n) j) ⁻¹ᵁ U).toScheme :=
  pullbackLineBundle ((pullback.snd (powerLocusProjection X o ho g n) j) ⁻¹ᵁ U).ι
    (pullbackLineBundle (pullback.fst (powerLocusProjection X o ho g n) j)
      (locusLineBundle X o ho g n))

/-- Canonical normalization of all three actual pullbacks, from the accepted
power coefficient to the power of the literal open-family line bundle. -/
def locusChartOpenLineBundlePowerIso (U : (Spec (.of R)).Opens) :
    let f := pullback.snd (powerLocusProjection X o ho g n) j
    let a := pullback.fst (powerLocusProjection X o ho g n) j
    (Modules.pullback (f ⁻¹ᵁ U).ι).obj
        ((Modules.pullback a).obj (powerLocusLineBundle X o ho g n).val) ≅
      (tensorPowerLineBundle _ (locusChartOpenLineBundle X o ho g n j U) n).val :=
  let a := pullback.fst (powerLocusProjection X o ho g n) j
  let b := ((pullback.snd (powerLocusProjection X o ho g n) j) ⁻¹ᵁ U).ι
  (Modules.pullback b).mapIso
    ((Modules.pullback a).mapIso (locusLineBundlePowerIso X o ho g n) ≪≫
      PowerPullback.pullbackPowerIso a (locusLineBundle X o ho g n) n) ≪≫
    PowerPullback.pullbackPowerIso b (pullbackLineBundle a (locusLineBundle X o ho g n)) n

/-- The positive prime-to-characteristic level remains invertible on the
actual total space of every chart open, through its original structure map. -/
theorem locusChartOpen_levelInvertible (U : (Spec (.of R)).Opens)
    (hunit : IsUnit (n : k)) :
    IsUnit (n : Γ(((pullback.snd (powerLocusProjection X o ho g n) j) ⁻¹ᵁ U).toScheme,
      ⊤)) := by
  let f := pullback.snd (powerLocusProjection X o ho g n) j
  let W : FScheme k := Over.mk ((f ⁻¹ᵁ U).ι ≫ f ≫ j ≫
    powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)
  simpa only [map_natCast] using hunit.map (constants W)

/-- Around every point of every actual affine chart there is one original
H1(mu_n) class whose original inclusion image is the literal bounded bundle.
The class is allowed the genuine global-units/n ambiguity. -/
theorem exists_locusChartOpen_kummerPreimage [IsOpenImmersion j]
    (hX : Properties X) (hn : 0 < n) (hunit : IsUnit (n : k)) (r : PrimeSpectrum R) :
    ∃ U : (Spec (.of R)).Opens, r ∈ U ∧
      ∃ ξ : Sheaf.H.{u + 2}
          (mu ((pullback.snd (powerLocusProjection X o ho g n) j) ⁻¹ᵁ U).toScheme n) 1,
        Sheaf.H.map (inclusion _ n) 1 ξ =
          EtaleCohomology.Picard.picardCohomologyEquiv _
            (classOf _ (locusChartOpenLineBundle X o ho g n j U)) := by
  obtain ⟨U, hr, ⟨τ⟩⟩ :=
    exists_powerLocusLineBundle_trivial_on_affine_base_open X o ho hX g n j r
  let e := (locusChartOpenLineBundlePowerIso X o ho g n j U).symm ≪≫ τ
  exact ⟨U, hr, EtaleCohomology.Picard.exists_lineBundle_kummerPreimage _
    (locusChartOpenLineBundle X o ho g n j U) n hn
    (locusChartOpen_levelInvertible X o ho g n j U hunit) e⟩

/-- Any actual geometric restriction of a family preimage retains the literal
pulled line-bundle class, under the original root-cohomology map. -/
theorem locusChartOpen_kummerPreimage_pullback (U : (Spec (.of R)).Opens)
    (hn : 0 < n) (hunit : IsUnit (n : k))
    {S : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} S)]
    (a : S ⟶ ((pullback.snd (powerLocusProjection X o ho g n) j) ⁻¹ᵁ U).toScheme)
    (ξ : Sheaf.H.{u + 2}
      (mu ((pullback.snd (powerLocusProjection X o ho g n) j) ⁻¹ᵁ U).toScheme n) 1)
    (hξ : Sheaf.H.map (inclusion _ n) 1 ξ =
      EtaleCohomology.Picard.picardCohomologyEquiv _
        (classOf _ (locusChartOpenLineBundle X o ho g n j U))) :
    Sheaf.H.map (inclusion S n) 1
        (EtaleCohomology.Kummer.rootsCohomologyPullback a n hn
          (locusChartOpen_levelInvertible X o ho g n j U hunit) 1 ξ) =
      EtaleCohomology.Picard.picardCohomologyEquiv S
        (classOf S (pullbackLineBundle a (locusChartOpenLineBundle X o ho g n j U))) :=
  EtaleCohomology.Picard.kummerPreimage_pullback a _ n hn
    (locusChartOpen_levelInvertible X o ho g n j U hunit) ξ hξ

end AffineChart

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
