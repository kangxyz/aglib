/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedQuotientRestriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.QuotientRestrictionComparison

/-! # Original quotient comparisons on smaller graded charts -/

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
  (e : P.restrict (formalGradedChart f I U) ≅ tilde (formalGradedLocalModule f I F U))

/-- The induced comparison uses the original restriction and chart quotient iso. -/
def formalGradedComparisonRestriction :
    P.restrict (formalGradedChart f I V) ≅ tilde (formalGradedLocalModule f I F V) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  exact quotientRestrictionComparison (formalGradedChart f I U) (formalGradedChart f I V)
    (formalGradedChartRestriction f I U V h) (formalGradedChartRestriction_chart f I U V h)
    e (formalGradedLocalRestrictionIso f I F U V h)

/-- The actual comparison on the smaller chart retains its original quotient map. -/
@[reassoc]
theorem formalGradedComparisonRestriction_quotient
    (q : formalGradedAmbient f I F ⟶ P)
    (he : (Scheme.Modules.restrictFunctor (formalGradedChart f I U)).map q ≫ e.hom =
      formalGradedLocalQuotient f I F U) :
    (Scheme.Modules.restrictFunctor (formalGradedChart f I V)).map q ≫
      (formalGradedComparisonRestriction f I F U V h P e).hom =
      formalGradedLocalQuotient f I F V := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  have hd := formalGradedLocalQuotient_restriction f I F U V h
  dsimp only [affineChartQuotientRestrictionEquation] at hd
  exact quotientRestrictionComparison_quotient _ _ _ _ q _ _ e _ he hd

/-- The comparison has the actual restriction square needed by pushforward gluing. -/
@[reassoc]
theorem formalGradedComparisonRestriction_square :
    ((restrictFunctorComp (formalGradedChartRestriction f I U V h)
      (formalGradedChart f I U)).symm.app P ≪≫
      (restrictFunctorCongr (formalGradedChartRestriction_chart f I U V h)).app P).hom ≫
        (formalGradedComparisonRestriction f I F U V h P e).hom =
      (Scheme.Modules.restrictFunctor (formalGradedChartRestriction f I U V h)).map e.hom ≫
        (formalGradedLocalRestrictionIso f I F U V h).hom := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  simp only [formalGradedComparisonRestriction, quotientRestrictionComparison,
    NatIso.trans_app, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Original quotient epis force the smaller-chart comparison, independently
of which member of the finite cover was used to construct it. -/
theorem formalGradedComparisonRestriction_unique
    (q : formalGradedAmbient f I F ⟶ P) [Epi q]
    (he : (Scheme.Modules.restrictFunctor (formalGradedChart f I U)).map q ≫ e.hom =
      formalGradedLocalQuotient f I F U)
    (d : P.restrict (formalGradedChart f I V) ≅ tilde (formalGradedLocalModule f I F V))
    (hd : (Scheme.Modules.restrictFunctor (formalGradedChart f I V)).map q ≫ d.hom =
      formalGradedLocalQuotient f I F V) :
    formalGradedComparisonRestriction f I F U V h P e = d := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.restrictFunctor (formalGradedChart f I V)).map q)).mp
  exact (formalGradedComparisonRestriction_quotient f I F U V h P e q he).trans hd.symm

/-- Any comparison retaining the same actual quotient has the original restriction square. -/
theorem formalGradedComparisonRestriction_square_of_quotient
    (q : formalGradedAmbient f I F ⟶ P) [Epi q]
    (he : (Scheme.Modules.restrictFunctor (formalGradedChart f I U)).map q ≫ e.hom =
      formalGradedLocalQuotient f I F U)
    (d : P.restrict (formalGradedChart f I V) ≅ tilde (formalGradedLocalModule f I F V))
    (hd : (Scheme.Modules.restrictFunctor (formalGradedChart f I V)).map q ≫ d.hom =
      formalGradedLocalQuotient f I F V) :
    (Scheme.Modules.restrictFunctor (formalGradedChartRestriction f I U V h)).map e.hom ≫
        (formalGradedLocalRestrictionIso f I F U V h).hom =
      ((restrictFunctorComp (formalGradedChartRestriction f I U V h)
        (formalGradedChart f I U)).symm.app P ≪≫
        (restrictFunctorCongr (formalGradedChartRestriction_chart f I U V h)).app P).hom ≫
          d.hom := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  rw [← formalGradedComparisonRestriction_unique f I F U V h P e q he d hd]
  exact (formalGradedComparisonRestriction_square f I F U V h P e).symm

end AlgebraicGeometry.Scheme.Cohomology
