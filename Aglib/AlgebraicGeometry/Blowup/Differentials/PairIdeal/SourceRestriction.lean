/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawSource
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorBidualOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FormsFiniteType


/-!
# Original blowup source on the original parameter chart

The source is the restriction of the raw bidual for the same global blowdown
and coefficient map. The original chart triangle identifies its structure
map with the actual affine composite. No local source line is substituted
for the original global source.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u


open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) [CommRing Λ] [CommRing R] [IsNoetherianRing R]
  [Algebra Λ R]
  [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))]
  (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I) (n : ℕ)

local notation "S" => Localization.Away.saturatedChart R I x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)

/-- The original blowup is locally Noetherian by its actual proper structural map. -/
theorem pairIdeal_blowup_isLocallyNoetherian :
    IsLocallyNoetherian (canonicalBlowup I) := by
  let : IsProper (blowdown I) := Blowup.BlowupDatum.isProper_of_isLocallyNoetherian B
  exact LocallyOfFiniteType.isLocallyNoetherian (blowdown I)

/-- The original composite structural map is locally of finite type. -/
theorem pairIdeal_structure_locallyOfFiniteType :
    LocallyOfFiniteType (blowdown I ≫ Spec.map α) := by
  let : IsProper (blowdown I) := Blowup.BlowupDatum.isProper_of_isLocallyNoetherian B
  exact locallyOfFiniteType_comp (blowdown I) (Spec.map α)

/-- The actual chart triangle and original raw restriction give the local source arrow. -/
def pairIdealBidualSourceMapOfCoherent
    (hM : QuasiCoherent.affineLocallyFiniteType (canonicalBlowup I)
      (moduleExteriorPower (canonicalBlowup I)
        (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n)) :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    (show (canonicalBlowup I).Modules from
      Invertible.dualSheaf (canonicalBlowup I) (Invertible.dualSheaf (canonicalBlowup I)
        (moduleExteriorPower (canonicalBlowup I)
          (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n))).restrict f ⟶
    Invertible.dualSheaf (Spec (.of S)) (Invertible.dualSheaf (Spec (.of S))
      (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n)) := by
  intro f hf
  let : IsLocallyNoetherian (canonicalBlowup I) :=
    pairIdeal_blowup_isLocallyNoetherian R I
  exact bidualFormsAffineRestrictionMapOfCoherent (blowdown I ≫ Spec.map α) n hM f ≫
    Invertible.doubleDualMap (Spec (.of S))
      (pairIdealRawChartCongruenceIso Λ R I x y hI n).hom

/-- The original finite-type interface supplies its original coherent source proof. -/
def pairIdealBidualSourceMap :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    (show (canonicalBlowup I).Modules from
      Invertible.dualSheaf (canonicalBlowup I) (Invertible.dualSheaf (canonicalBlowup I)
        (moduleExteriorPower (canonicalBlowup I)
          (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n))).restrict f ⟶
    Invertible.dualSheaf (Spec (.of S)) (Invertible.dualSheaf (Spec (.of S))
      (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n)) := by
  let : LocallyOfFiniteType (blowdown I ≫ Spec.map α) :=
    pairIdeal_structure_locallyOfFiniteType Λ R I
  exact pairIdealBidualSourceMapOfCoherent Λ R I x y hI n
    (rawForms_affineLocallyFiniteType (blowdown I ≫ Spec.map α) n)

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
