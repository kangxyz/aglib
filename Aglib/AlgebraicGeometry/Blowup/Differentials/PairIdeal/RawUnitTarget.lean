/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawSource
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawTarget
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleTarget
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.RawUnitTarget
public import Aglib.AlgebraicGeometry.Blowup.Differentials.UnitMap
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient


/-!
# The original raw target unit law for the supplied ideal

Transport the accepted saturated-pair unit law once along the original
parameter-ideal equality. The original whole chart-base comparison and
original target/unit maps are retained; no desired square is a premise.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup.RegularPair
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "S" => Localization.Away.saturatedChart R I x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)

local notation "M" => moduleExteriorPower (Spec (CommRingCat.of R))
  (relativeDifferentialSheaf (Spec.map α)) n
local notation "σ" => CommRingCat.ofHom (algebraMap R S)

/-- The original raw target unit equation on the supplied ideal's chart. -/
theorem pairIdealOnePoleRawTargetMap_unit :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    (pairIdealChartBasePullbackIso R I x y hI).hom.app M ≫
        rawFormsPullback (Spec.map α) (Spec.map σ) n ≫
        pairIdealOnePoleRawTargetMap Λ R K I x y hI hx hy n L φ =
      (pullback f).map (pairIdealOnePoleUnitMap Λ R I n L φ) := by
  subst I
  have h := saturatedPairOnePoleRawTargetMap_unit Λ R K x y hx hy n L φ
  dsimp only [pairIdealOnePoleRawTargetMap, saturatedPairChartBasePullbackIso,
    saturatedPairOnePoleTarget, Insert.insert, Singleton.singleton,
    Set.instInsert, Set.instSingletonSet] at h ⊢
  exact h

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
