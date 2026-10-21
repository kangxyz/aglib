/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPushforwardCharts
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedComparisonRestriction

/-! # Original pushforward restriction from retained quotient equations -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  (U V : X.affineOpens) (h : V.val ≤ U.val)
  (P : (formalGradedSpace f I).Modules)
  (eU : P.restrict (formalGradedChart f I U) ≅ tilde (formalGradedLocalModule f I F U))
  (eV : P.restrict (formalGradedChart f I V) ≅ tilde (formalGradedLocalModule f I F V))
  (q : formalGradedAmbient f I F ⟶ P) [Epi q]

/-- The retained original quotient equations force the native pushforward restriction square. -/
theorem formalGradedPushforwardChartIso_restriction_of_quotients
    (heU : (Scheme.Modules.restrictFunctor (formalGradedChart f I U)).map q ≫ eU.hom =
      formalGradedLocalQuotient f I F U)
    (heV : (Scheme.Modules.restrictFunctor (formalGradedChart f I V)).map q ≫ eV.hom =
      formalGradedLocalQuotient f I F V) :
    letI : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op)) := by
      have hc := U.property.map_fromSpec V.property (homOfLE h).op
      have : IsOpenImmersion
          (Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.property.fromSpec) :=
        hc ▸ inferInstance
      exact IsOpenImmersion.of_comp _ U.property.fromSpec
    RestrictionComparisonSquare U.property.fromSpec V.property.fromSpec
      (Spec.map (X.presheaf.map (homOfLE h).op))
      (U.property.map_fromSpec V.property (homOfLE h).op)
      ((Scheme.Modules.pushforward (formalGradedProjection f I)).obj P) F.gradedUnderlying
      (formalGradedPushforwardChartIso f I F U P eU).hom
      (formalGradedPushforwardChartIso f I F V P eV).hom := by
  let : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op)) := by
    have hc := U.property.map_fromSpec V.property (homOfLE h).op
    have : IsOpenImmersion
        (Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.property.fromSpec) :=
      hc ▸ inferInstance
    exact IsOpenImmersion.of_comp _ U.property.fromSpec
  exact formalGradedPushforwardChartIso_restriction f I F U V h P eU eV
    (formalGradedComparisonRestriction_square_of_quotient f I F U V h P eU q heU eV heV)

end AlgebraicGeometry.Scheme.Cohomology
