/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalPushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction

/-! # Original section maps of the graded pushforward comparison -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The original local pushforward comparison on sections is the scalar
forgetful comparison followed by the actual coproduct section identification. -/
theorem formalGradedLocalPushforwardIso_sections (U : X.affineOpens) :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule_scalarTower_left f I F U
    letI : F.gradedUnderlying.IsQuasicoherent :=
      QuasiCoherent.quasicoherent_coproduct F.gradedPiece
    moduleSpecΓFunctor.map (formalGradedLocalPushforwardIso f I F U).hom ≫
        (affineChartΓIso U F.gradedUnderlying).hom ≫
        (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).hom =
      (pushforwardGlobalSectionsIso (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)))).hom.app
          (tilde (formalGradedLocalModule f I F U)) ≫
        (ModuleCat.restrictScalars
          (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))).map
            ((tilde.toTildeΓNatIso (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))).app
               (formalGradedLocalModule f I F U)).inv ≫
        (formalGradedLocalForgetIso f I F U).hom := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule_scalarTower_left f I F U
  let : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  let N := ModuleCat.of Γ(X, U) (⨁ n, Γ(F.gradedPiece n, U))
  let e := affineChartΓIso U F.gradedUnderlying ≪≫
    QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U
  have he : moduleSpecΓFunctor.map (formalGradedCoproductChartIso f I F U).hom ≫
      ((tilde.toTildeΓNatIso (R := CommRingCat.of Γ(X, U))).app N).inv = e.hom :=
    affineSheafIsoOfSectionIso_sections
      (F.gradedUnderlying.restrict U.property.fromSpec) N e
  change moduleSpecΓFunctor.map (formalGradedLocalPushforwardIso f I F U).hom ≫
    e.hom = _
  rw [← he]
  simp only [formalGradedLocalPushforwardIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hc : moduleSpecΓFunctor.map (formalGradedCoproductChartIso f I F U).inv ≫
      moduleSpecΓFunctor.map (formalGradedCoproductChartIso f I F U).hom ≫
      ((tilde.toTildeΓNatIso (R := CommRingCat.of Γ(X, U))).app
         N).inv = ((tilde.toTildeΓNatIso (R := CommRingCat.of Γ(X, U))).app N).inv := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hc, tildePushforwardIso_globalSections_unit]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((tilde.adjunction (R := CommRingCat.of Γ(X, U))).unit.app _)]
  erw [← (tilde.adjunction (R := CommRingCat.of Γ(X, U))).unit.naturality
    (formalGradedLocalForgetIso f I F U).hom]
  simp only [Category.assoc]
  change _ ≫ _ ≫ (formalGradedLocalForgetIso f I F U).hom ≫
    ((tilde.toTildeΓNatIso (R := CommRingCat.of Γ(X, U))).app
       N).hom ≫ ((tilde.toTildeΓNatIso (R := CommRingCat.of Γ(X, U))).app N).inv = _
  simp only [Iso.hom_inv_id, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
