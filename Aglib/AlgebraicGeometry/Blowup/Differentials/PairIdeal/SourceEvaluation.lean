/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawSource
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.SourceRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenIsoEvaluation
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FormsFiniteType


/-!
# Original evaluation on the original ideal-blowup chart

The existing global-bidual source arrow preserves original evaluation,
including the actual raw chart isomorphism. This forward equation uses the
passed restriction evaluation square and native bidual naturality. It does
not require a comparison of the entire bidual source arrow or cancel raw
evaluation.
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

local notation "Y" => canonicalBlowup I
local notation "M" => moduleExteriorPower Y
  (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n

omit [LocallyOfFiniteType (Spec.map α)] in
/-- The original chart source arrow preserves the original raw evaluation. -/
theorem pairIdeal_bidualSourceMapOfCoherent_evaluation
    (hM : QuasiCoherent.affineLocallyFiniteType (canonicalBlowup I)
      (moduleExteriorPower (canonicalBlowup I)
        (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n)) :
    let f : Spec (.of S) ⟶ Y := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    (Scheme.Modules.restrictFunctor f).map (Invertible.bidualMap Y M) ≫
        pairIdeal_bidualSourceMapOfCoherent Λ R I x y hI n hM =
      (pairIdeal_rawSourceIso Λ R I x y hI n).hom ≫
        Invertible.bidualMap (Spec (.of S))
          (moduleExteriorPower (Spec (.of S))
            (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) := by
  intro f hf
  let : IsLocallyNoetherian Y := pairIdeal_blowup_isLocallyNoetherian R I
  exact bidualFormsAffineRestrictionMapOfCoherent_iso_evaluation
    (blowdown I ≫ Spec.map α) f n hM
    (moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n)
    (pairIdeal_rawChartCongruenceIso Λ R I x y hI n)

/-- The original finite-type interface supplies its original coherent source proof. -/
theorem pairIdeal_bidualSourceMap_evaluation :
    let f : Spec (.of S) ⟶ Y := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    (Scheme.Modules.restrictFunctor f).map (Invertible.bidualMap Y M) ≫
        pairIdeal_bidualSourceMap Λ R I x y hI n =
      (pairIdeal_rawSourceIso Λ R I x y hI n).hom ≫
        Invertible.bidualMap (Spec (.of S))
          (moduleExteriorPower (Spec (.of S))
            (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) := by
  let : LocallyOfFiniteType (blowdown I ≫ Spec.map α) :=
    pairIdeal_structure_locallyOfFiniteType Λ R I
  exact pairIdeal_bidualSourceMapOfCoherent_evaluation Λ R I x y hI n
    (rawForms_affineLocallyFiniteType (blowdown I ≫ Spec.map α) n)

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
