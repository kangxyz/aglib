/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ChartNonempty
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawFamily
public import Aglib.AlgebraicGeometry.Blowup.Differentials.UnitLocus
public import Aglib.AlgebraicGeometry.Blowup.Differentials.UnitMap
public import Aglib.AlgebraicGeometry.Blowup.Integral.NonzeroIdeal
public import Aglib.AlgebraicGeometry.Blowup.PairIdeal.Cover
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Invertible.GenericUniqueness.OpenGluing
public import Aglib.AlgebraicGeometry.Spec.LocalizationNonempty


/-!
# Gluing the original raw one-pole maps on the same blowup

Actual local unit squares, the original unit-locus isomorphism and ordinary
line-target uniqueness prove overlap compatibility internally. The actual
full original two-chart cover then glues the original raw maps uniquely.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (hproper : I ≠ ⊤) (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "X" => canonicalBlowup I
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "M" => moduleExteriorPower X
  (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n
local notation "T" => Invertible.tensorLineBundle X
  (Invertible.pullbackLineBundle (blowdown I) L)
  (Invertible.dualLineBundle X (centreIdealLine I))

omit [IsNoetherianRing R] in
/-- The original raw chart maps glue uniquely, with no compatibility or generic-square premise. -/
theorem existsUnique_pairIdeal_onePoleRawMap :
    ∃! κ : M ⟶ Subtype.val T,
      ∀ i : Bool, (Scheme.Modules.restrictFunctor (pairIdealChart I x y hI i)).map κ =
        pairIdeal_onePoleRawFamily Λ R K I x y hI hx hy hproper n L φ i := by
  have hx0 : x ≠ 0 := by
    intro h
    exact one_ne_zero (hx (by simp [h]))
  have hxI : x ∈ I := hI ▸ Ideal.subset_span (Set.mem_insert x {y})
  let _ : IsIntegral X := idealBlowup_isIntegral_of_mem_ne_zero I x hxI hx0
  let _ : Nonempty (Spec (.of (Localization.Away x))) := awaySpec_nonempty R K x hx0
  let (i : Bool) : Nonempty (pairIdealChartScheme I x y hI i) :=
    pairIdealChart_nonempty R K I x y hI hx hy hproper i
  let B := Blowup.blowupDatum (Blowup.affineCenter R I)
  let H := Blowup.affineAtlas B
  let j : Spec (.of (Localization.Away x)) ⟶ X :=
    Blowup.UnitLocus.unitChartMap H (firstGenerator I x y hI)
  let _ : IsOpenImmersion j :=
    Blowup.UnitLocus.unitChartMap_isOpenImmersion H (firstGenerator I x y hI)
  let β := rawFormsPullback (Spec.map α) (blowdown I) n
  let t := pairIdeal_onePoleUnitMap Λ R I n L φ
  let r := pairIdeal_onePoleRawFamily Λ R K I x y hI hx hy hproper n L φ
  let _ : IsIso ((pullback j).map β) :=
    ideal_rawPullback_unitChart_isIso Λ R I (firstGenerator I x y hI) n
  have hr := pairIdeal_onePoleRawFamily_unit Λ R K I x y hI hx hy hproper n L φ
  exact existsUnique_restrictionHom_of_openUnitSquares j β T t
    (pairIdealChartScheme I x y hI) (pairIdealChart I x y hI)
    (pairIdealCharts_cover I x y hI) r hr

/-- The unique global raw map selected by the original chart maps and original native gluing. -/
def pairIdeal_onePoleRawMap : M ⟶ Subtype.val T :=
  (existsUnique_pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n L φ).choose

omit [IsNoetherianRing R] in
/-- The actual global raw map restricts to every original local raw map. -/
theorem pairIdeal_onePoleRawMap_restrict (i : Bool) :
    (Scheme.Modules.restrictFunctor (pairIdealChart I x y hI i)).map
        (pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n L φ) =
      pairIdeal_onePoleRawFamily Λ R K I x y hI hx hy hproper n L φ i :=
  (existsUnique_pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n L φ).choose_spec.1 i

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
