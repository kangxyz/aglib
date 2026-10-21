/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedChartIntersection
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedQuotientRestriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.OverlapQuotient

/-! # Actual local coefficient comparisons on categorical chart overlaps -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : Coherent.AdicSystem X (idealThickeningIdealSheaf f I))
  (U V W : X.affineOpens) (hWU : W.val ≤ U.val) (hWV : W.val ≤ V.val)
  (hW : W.val = U.val ⊓ V.val)

/-- The original local graded modules agree on the actual categorical overlap.
Both factors are compared to the actual module on the affine intersection. -/
def formalGradedOverlapIso :
    letI (T : X.Opens) : Algebra A Γ(X, T) := formalGradedSectionAlgebra f T
    (tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F U)).restrict
        (pullback.fst (formalGradedChart f I U) (formalGradedChart f I V)) ≅
      (tilde (R := CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F V)).restrict
        (pullback.snd (formalGradedChart f I U) (formalGradedChart f I V)) := by
  let (T : X.Opens) : Algebra A Γ(X, T) := formalGradedSectionAlgebra f T
  let H := formalGradedChartIntersection_isPullback f I U V W hWU hWV hW
  let l := H.isoPullback.inv
  let a := formalGradedChartRestriction f I U W hWU
  let b := formalGradedChartRestriction f I V W hWV
  let eU := (restrictFunctorCongr H.isoPullback_inv_fst).symm.app
      (tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F U)) ≪≫
    (restrictFunctorComp l a).app (tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F U))
  let eV := (restrictFunctorCongr H.isoPullback_inv_snd).symm.app
      (tilde (R := CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F V)) ≪≫
    (restrictFunctorComp l b).app (tilde (R := CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F V))
  exact eU ≪≫ (Scheme.Modules.restrictFunctor l).mapIso
    (formalGradedLocalRestrictionIso f I F U W hWU ≪≫
      (formalGradedLocalRestrictionIso f I F V W hWV).symm) ≪≫ eV.symm

/-- The actual overlap comparison preserves the original canonical quotient maps. -/
@[reassoc]
theorem formalGradedOverlapIso_quotient :
    letI (T : X.Opens) : Algebra A Γ(X, T) := formalGradedSectionAlgebra f T
    (Scheme.Modules.restrictFunctor (pullback.fst (formalGradedChart f I U)
      (formalGradedChart f I V))).map (formalGradedLocalQuotient f I F U) ≫
        (formalGradedOverlapIso f I F U V W hWU hWV hW).hom =
      (overlapRestrictIso (formalGradedChart f I U) (formalGradedChart f I V)).hom.app
        (formalGradedAmbient f I F) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (formalGradedChart f I U)
        (formalGradedChart f I V))).map (formalGradedLocalQuotient f I F V) := by
  let (T : X.Opens) : Algebra A Γ(X, T) := formalGradedSectionAlgebra f T
  exact overlapRestrictIso_refinement_quotient
    (formalGradedChartRestriction f I U W hWU)
    (formalGradedChartRestriction f I V W hWV)
    (formalGradedChart f I U) (formalGradedChart f I V) (formalGradedChart f I W)
    (formalGradedChartIntersection_isPullback f I U V W hWU hWV hW)
    (formalGradedChartRestriction_chart f I U W hWU)
    (formalGradedChartRestriction_chart f I V W hWV)
    (formalGradedAmbient f I F)
    (tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F U))
    (tilde (R := CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F V))
    (tilde (R := CommRingCat.of (Γ(X, W) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F W))
    (formalGradedLocalQuotient f I F U) (formalGradedLocalQuotient f I F V)
    (formalGradedLocalQuotient f I F W)
    (formalGradedLocalRestrictionIso f I F U W hWU)
    (formalGradedLocalRestrictionIso f I F V W hWV)
    (formalGradedLocalQuotient_restriction f I F U W hWU)
    (formalGradedLocalQuotient_restriction f I F V W hWV)

end AlgebraicGeometry.Scheme.Cohomology
