/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleChart
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleRaw
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleSquare
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# The original raw one-pole map has the original exceptional unit square

The existing bidual unit square is evaluated on the original raw source.
This uses the proved extension/evaluation equation, not cancellation of
that evaluation map. The same original exceptional section is retained.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (x y : R)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "I" => Ideal.span (Set.insert x (Set.singleton y))
local notation "S" => Localization.Away.saturatedChart R I x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)
local notation "c" => chartMap B (firstGenerator I x y rfl)

/-- Original raw evaluation recovers exactly the same raw one-pole composite. -/
theorem saturatedPair_onePoleChartMap_evaluation :
    Invertible.bidualMap (Spec (.of S))
      (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) ≫
      saturatedPair_onePoleChartMap Λ R K x y hx hy n L φ =
        saturatedPair_onePoleRawMap Λ R K x y hx hy n L φ := by
  have he := saturatedPair_onePoleChartMap_eq_extension Λ R K x y hx hy n L φ
  exact (congrArg (fun t => Invertible.bidualMap (Spec (.of S))
    (moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) ≫ t) he).trans
        (Invertible.extendToBidualLine_evaluation (Spec (.of S))
          (saturatedPair_onePoleLine R x y L)
          (saturatedPair_onePoleRawMap Λ R K x y hx hy n L φ))

/-- The original raw arrow has the same original structural-unit/exceptional-section square. -/
theorem saturatedPair_onePoleRawMap_unit :
    let f : Spec (.of S) ⟶ canonicalBlowup I := c
    let s : SheafOfModules.unit (canonicalBlowup I).ringCatSheaf ⟶
        (Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val :=
      cartierDualIdealSection (centreι B)
    rawFormsPullback (Spec.map α) (Spec.map σ) n ≫
      saturatedPair_onePoleRawMap Λ R K x y hx hy n L φ =
    (pullback (Spec.map σ)).map φ ≫
      (positiveCartierTensorSection (Spec (.of S))
        (saturatedPair_exceptionalPositiveLine R x y).val
        ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app
          ((pullback (Spec.map σ)).obj L.val) ≫
      (tensorSheafBraiding (Spec (.of S)) (saturatedPair_exceptionalPositiveLine R x y).val
        ((pullback (Spec.map σ)).obj L.val)).hom := by
  intro f s
  exact (congrArg (fun t => rawFormsPullback (Spec.map α) (Spec.map σ) n ≫ t)
    (saturatedPair_onePoleChartMap_evaluation Λ R K x y hx hy n L φ)).symm.trans
      (saturatedPair_onePoleChartMap_unit Λ R K x y hx hy n L φ)

end AlgebraicGeometry.Scheme.Blowup.RegularPair
