/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.IdealFrames
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Charts
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorChartSquare
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenRestriction


/-!
# Original raw source on the same parameter chart

The actual open-restriction comparison and original atlas triangle identify
the restriction of the same global raw exterior sheaf with its affine raw
forms. This requires no bidual, normality or finite-type hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u


open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) [CommRing Λ] [CommRing R] [Algebra Λ R]
  (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I) (n : ℕ)

local notation "S" => Localization.Away.saturatedChart R I x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)

/-- The original chart open-immersion witness, retained by both source constructions. -/
theorem pairIdeal_chart_isOpenImmersion :
    IsOpenImmersion (chartMap B (firstGenerator I x y hI)) :=
  (Blowup.affineAtlas B).openImmersion (firstGenerator I x y hI)

/-- The original atlas triangle with its literal parameter-chart source and base map. -/
theorem pairIdeal_chartBase_triangle :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    f ≫ blowdown I = Spec.map σ := by
  intro f
  exact (Blowup.affineAtlas B).triangle (firstGenerator I x y hI)

/-- The original whole chart-base pullback comparison, with its literal chart carrier. -/
def pairIdealChartBasePullbackIso :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    pullback (blowdown I) ⋙ pullback f ≅ pullback (Spec.map σ) := by
  intro f
  exact pullbackComp f (blowdown I) ≪≫
    pullbackCongr (pairIdeal_chartBase_triangle R I x y hI)

/-- The single original chart-triangle congruence for the same raw exterior modules. -/
def pairIdealRawChartCongruenceIso :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (f ≫ (blowdown I ≫ Spec.map α))) n ≅
    moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n := by
  intro f
  have ht : f ≫ (blowdown I ≫ Spec.map α) = Spec.map σ ≫ Spec.map α :=
    (Category.assoc f (blowdown I) (Spec.map α)).symm.trans
      (congrArg (fun t => t ≫ Spec.map α)
        (pairIdeal_chartBase_triangle R I x y hI))
  exact (moduleExteriorPowerFunctor (Spec (.of S)) n).mapIso
    (relativeDifferentialCongrIso (f ≫ (blowdown I ≫ Spec.map α)) ht)

/-- The original raw source isomorphism on the supplied original ideal's chart. -/
def pairIdealRawSourceIso :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    (moduleExteriorPower (canonicalBlowup I)
      (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n).restrict f ≅
    moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n := by
  intro f hf
  exact rawFormsOpenIso (blowdown I ≫ Spec.map α) f n ≪≫
    pairIdealRawChartCongruenceIso Λ R I x y hI n

local notation "M" => moduleExteriorPower (canonicalBlowup I)
  (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n
local notation "P" => moduleExteriorPower (Spec (CommRingCat.of R))
  (relativeDifferentialSheaf (Spec.map α)) n

/-- The original whole raw source iso compares the actual restricted pullback map. -/
theorem pairIdealRawSourceIso_pullback :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    let c := pairIdealChartBasePullbackIso R I x y hI
    (pullback f).map (rawFormsPullback (Spec.map α) (blowdown I) n) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app M ≫
        (pairIdealRawSourceIso Λ R I x y hI n).hom =
      c.hom.app P ≫ rawFormsPullback (Spec.map α) (Spec.map σ) n := by
  intro f hf c
  simpa only [c, pairIdealChartBasePullbackIso, pairIdealRawSourceIso,
    pairIdealRawChartCongruenceIso] using
    (rawFormsPullback_openTriangle_iso (Spec.map α) (blowdown I) f (Spec.map σ)
      (pairIdeal_chartBase_triangle R I x y hI) n)


end AlgebraicGeometry.Scheme.Blowup.PairIdeal
