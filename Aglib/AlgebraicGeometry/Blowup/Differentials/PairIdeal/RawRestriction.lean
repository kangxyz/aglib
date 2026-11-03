/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawSource
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawTarget


/-!
# Original raw one-pole maps between restrictions of the same global objects

Use the actual raw source isomorphism, the existing raw target map and the
original target restriction/pullback comparison. Both parameter orders
retain the same original ideal, blowup, raw sheaf and target line.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "Y" => canonicalBlowup I
local notation "S" => Localization.Away.saturatedChart R I x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)
local notation "M" => moduleExteriorPower Y (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n
local notation "T" => centreTwistedPullbackLine I L

/-- The original raw chart map now has a common original global source and target. -/
def pairIdealOnePoleRawRestrictionMap :
    let f : Spec (.of S) ⟶ Y := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    (Scheme.Modules.restrictFunctor f).obj M ⟶ (Scheme.Modules.restrictFunctor f).obj (T).val := by
  intro f hf
  let g : (Scheme.Modules.restrictFunctor f).obj M ⟶ (pullback f).obj (T).val :=
    (pairIdealRawSourceIso Λ R I x y hI n).hom ≫
      pairIdealOnePoleRawTargetMap Λ R K I x y hI hx hy n L φ
  exact g ≫ (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (T).val

/-- The original raw restriction map is its original source/target composite followed by
 the inverse component of the same restriction/pullback comparison. -/
theorem pairIdealOnePoleRawRestrictionMap_eq :
    let f : Spec (.of S) ⟶ Y := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    pairIdealOnePoleRawRestrictionMap Λ R K I x y hI hx hy n L φ =
      ((pairIdealRawSourceIso Λ R I x y hI n).hom ≫
        pairIdealOnePoleRawTargetMap Λ R K I x y hI hx hy n L φ) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (T).val := by
  intro f hf
  rfl

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
