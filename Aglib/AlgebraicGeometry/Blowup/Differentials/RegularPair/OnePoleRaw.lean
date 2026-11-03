/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleChart
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleTarget
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.ScaledSheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Naturality


/-!
# The original one-pole bidual maps extend their original raw maps

Use the already constructed scaled raw map and the same inverse-ideal frame.
The original bidual chart map and original global-target chart map are
proved to be the canonical extensions of these raw composites. They are
not replaced by a newly selected bidual map.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Modules.Invertible

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

/-- The original raw map followed by the original inverse-ideal frame. -/
def saturatedPairOnePoleRawMap :
    moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n ⟶
    (saturatedPairOnePoleLine R x y L).val :=
  saturatedPairScaledRawMap Λ R K x y hx hy n L φ ≫
    (saturatedPairOnePoleFrame R x y L).hom

/-- The existing bidual chart map is exactly the extension of its original raw map. -/
theorem saturatedPairOnePoleChartMap_eq_extension :
    saturatedPairOnePoleChartMap Λ R K x y hx hy n L φ =
    Invertible.extendToBidualLine (Spec (.of S)) (saturatedPairOnePoleLine R x y L)
      (saturatedPairOnePoleRawMap Λ R K x y hx hy n L φ) :=
  Invertible.extendToBidualLine_postcomp
    (Invertible.pullbackLineBundle (Spec.map σ) L) (saturatedPairOnePoleLine R x y L)
    (saturatedPairScaledRawMap Λ R K x y hx hy n L φ)
    (saturatedPairOnePoleFrame R x y L).hom

/-- The same raw composite with the original common global target. -/
def saturatedPairOnePoleRawTargetMap :
    moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n ⟶
    (pullback c).obj (saturatedPairOnePoleTarget R x y L).val :=
  saturatedPairOnePoleRawMap Λ R K x y hx hy n L φ ≫
    (saturatedPairOnePoleTargetIso R x y L).inv

/-- The original global-target map is the same canonical raw extension. -/
theorem saturatedPairOnePoleTargetMap_eq_extension :
    saturatedPairOnePoleTargetMap Λ R K x y hx hy n L φ =
    Invertible.extendToBidualLine (Spec (.of S))
      (Invertible.pullbackLineBundle c (saturatedPairOnePoleTarget R x y L))
      (saturatedPairOnePoleRawTargetMap Λ R K x y hx hy n L φ) := by
  have h := Invertible.extendToBidualLine_postcomp (saturatedPairOnePoleLine R x y L)
    (Invertible.pullbackLineBundle c (saturatedPairOnePoleTarget R x y L))
    (saturatedPairOnePoleRawMap Λ R K x y hx hy n L φ)
    (saturatedPairOnePoleTargetIso R x y L).inv
  exact (congrArg (fun t => t ≫ (saturatedPairOnePoleTargetIso R x y L).inv)
    (saturatedPairOnePoleChartMap_eq_extension Λ R K x y hx hy n L φ)).trans h

end AlgebraicGeometry.Scheme.Blowup.RegularPair
