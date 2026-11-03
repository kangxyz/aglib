/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.ScaledBidual
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Frames
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Frame


/-!
# The actual inverse-ideal-frame one-pole chart map

The original saturated chart's exceptional ideal frame is dualized by the
native evaluation frame. Tensoring the constructed scaled bidual map with
this inverse-ideal frame gives a map into the actual pulled-back base line
tensored with the actual exceptional positive line. Its frame coordinate
is exactly the original scaled map; global overlap gluing is not asserted.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

open AlgebraicGeometry.Scheme.Blowup.RegularPoint
open AlgebraicGeometry.Scheme.Blowup.IdealFrames

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

local notation "S" =>
  Localization.Away.saturatedChart R (Ideal.span (Set.insert x (Set.singleton y))) x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)

local notation "I" => Ideal.span (Set.insert x (Set.singleton y))
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)
local notation "a" => firstGenerator I x y rfl
local notation "c" => chartMap B a

/-- The positive exceptional line is the pullback of the dual of the actual
centre ideal on the same constructed blowup. -/
def saturatedPairExceptionalPositiveLine : Invertible.LineBundle (Spec (.of S)) :=
  Invertible.pullbackLineBundle c
    (Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I))

/-- Its frame is obtained from the original denominator ideal frame by
native dual evaluation, not by choosing a rational trivialization. -/
def saturatedPairExceptionalPositiveFrame :
    SheafOfModules.unit (Spec (.of S)).ringCatSheaf ≅
      (saturatedPairExceptionalPositiveLine R x y).val :=
  dualPullbackFrame c (centreIdealLine I) (chartFrame B a)

/-- The actual local one-pole target keeps both original factors. -/
def saturatedPairOnePoleLine : Invertible.LineBundle (Spec (.of S)) :=
  Invertible.tensorLineBundle (Spec (.of S))
    (Invertible.pullbackLineBundle (Spec.map σ) L)
    (saturatedPairExceptionalPositiveLine R x y)

/-- Tensor the original pulled-back line with the actual inverse ideal frame. -/
def saturatedPairOnePoleFrame :
    (pullback (Spec.map σ)).obj L.val ≅ (saturatedPairOnePoleLine R x y L).val :=
  (tensorSheafLeftUnit (Spec (.of S)) ((pullback (Spec.map σ)).obj L.val)).symm ≪≫
    tensorSheafIso (Spec (.of S)) (saturatedPairExceptionalPositiveFrame R x y)
      (Iso.refl _) ≪≫
    tensorSheafBraiding (Spec (.of S)) (saturatedPairExceptionalPositiveLine R x y).val
      ((pullback (Spec.map σ)).obj L.val)

/-- The actual local bidual map with one positive exceptional twist. -/
def saturatedPairOnePoleChartMap :
    Invertible.dualSheaf (Spec (.of S)) (Invertible.dualSheaf (Spec (.of S))
      (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n)) ⟶
    (saturatedPairOnePoleLine R x y L).val :=
  saturatedPairScaledBidualMap Λ R K x y hx hy n L φ ≫
    (saturatedPairOnePoleFrame R x y L).hom

/-- In the actual inverse-ideal frame, the constructed one-pole map has
exactly the original scaled coefficient, with no replacement scalar. -/
theorem saturatedPairOnePoleChartMap_coordinate :
    saturatedPairOnePoleChartMap Λ R K x y hx hy n L φ ≫
      (saturatedPairOnePoleFrame R x y L).inv =
    saturatedPairScaledBidualMap Λ R K x y hx hy n L φ := by
  let f := saturatedPairScaledBidualMap Λ R K x y hx hy n L φ
  let e := saturatedPairOnePoleFrame R x y L
  exact (Category.assoc f e.hom e.inv).trans
    ((congrArg (fun t => f ≫ t) e.hom_inv_id).trans (Category.comp_id f))

end AlgebraicGeometry.Scheme.Blowup.RegularPair
