/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawSource
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleChart
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.TwistedLine


/-!
# The one-pole chart target is the original global tensor line

The original chart triangle and canonical pullback tensor/composition
comparisons identify the chart target with the pullback of the same actual
line on the original blowup. No replacement blowup or line is selected.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

open AlgebraicGeometry.Scheme.Blowup.RegularPoint
open AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Blowup.PairIdeal

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

/-- The actual global one-pole target on the same constructed blowup. -/
def saturatedPairOnePoleTarget : Invertible.LineBundle (canonicalBlowup I) :=
  centreTwistedPullbackLine I L

omit [IsDomain R] in
/-- The original chart triangle, retained once before applying pullback comparisons. -/
theorem saturatedPair_chartBase_triangle : c ≫ blowdown I = Spec.map σ :=
  pairIdeal_chartBase_triangle R I x y rfl

/-- The original whole pullback comparison, before evaluation on a module. -/
def saturatedPairChartBasePullbackIso :
    let f : Spec (.of S) ⟶ canonicalBlowup I := c
    pullback (blowdown I) ⋙ pullback f ≅ pullback (Spec.map σ) :=
  pairIdealChartBasePullbackIso R I x y rfl

/-- The original chart triangle identifies the actual pulled-back base line. -/
def saturatedPairChartBaseLineIso :
    (pullback c).obj ((pullback (blowdown I)).obj L.val) ≅
      (pullback (Spec.map σ)).obj L.val :=
  (saturatedPairChartBasePullbackIso R x y).app L.val

/-- The original global tensor line restricts to the constructed chart target. -/
def saturatedPairOnePoleTargetIso :
    (pullback c).obj (saturatedPairOnePoleTarget R x y L).val ≅
      (saturatedPairOnePoleLine R x y L).val :=
  Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso c
      (Invertible.pullbackLineBundle (blowdown I) L)
      (Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I)) ≪≫
    tensorSheafIso (Spec (.of S)) (saturatedPairChartBaseLineIso R x y L) (Iso.refl _)

omit [IsDomain R] in
/-- The original target comparison has the retained whole-comparison component. -/
theorem saturatedPairOnePoleTargetIso_hom :
    let f : Spec (.of S) ⟶ canonicalBlowup I := c
    let e := saturatedPairChartBasePullbackIso R x y
    let P := Invertible.pullbackLineBundle (blowdown I) L
    let N := Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I)
    let U := Invertible.pullbackLineBundle (Spec.map σ) L
    let t : (pullback f).obj (Invertible.tensorLineBundle (canonicalBlowup I) P N).val ≅
        (Invertible.tensorLineBundle (Spec (.of S)) U
          (Invertible.pullbackLineBundle f N)).val := saturatedPairOnePoleTargetIso R x y L
    t.hom =
      (Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso f P N ≪≫
        tensorSheafIso (Spec (.of S)) (e.app L.val) (Iso.refl _)).hom := by
  rfl

/-- The same constructed map lands in the pullback of the original global target. -/
def saturatedPairOnePoleTargetMap :
    Invertible.dualSheaf (Spec (.of S)) (Invertible.dualSheaf (Spec (.of S))
      (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n)) ⟶
    (pullback c).obj (saturatedPairOnePoleTarget R x y L).val :=
  saturatedPairOnePoleChartMap Λ R K x y hx hy n L φ ≫
    (saturatedPairOnePoleTargetIso R x y L).inv

/-- The original target comparison recovers exactly the same chart map. -/
theorem saturatedPairOnePoleTargetMap_compare :
    saturatedPairOnePoleTargetMap Λ R K x y hx hy n L φ ≫
      (saturatedPairOnePoleTargetIso R x y L).hom =
    saturatedPairOnePoleChartMap Λ R K x y hx hy n L φ := by
  let g := saturatedPairOnePoleChartMap Λ R K x y hx hy n L φ
  let e := saturatedPairOnePoleTargetIso R x y L
  exact (Category.assoc g e.inv e.hom).trans
    ((congrArg (fun t => g ≫ t) e.inv_hom_id).trans (Category.comp_id g))

end AlgebraicGeometry.Scheme.Blowup.RegularPair
