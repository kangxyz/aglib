/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSectionNaturality

/-! # Original coefficient maps under the local graded pushforward comparison -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)
  (U : X.affineOpens)

/-- The local pushforward comparison retains the actual coproduct of original
graded coefficient maps. -/
theorem formalGradedLocalPushforwardIso_naturality :
  letI := formalGradedSectionAlgebra f U
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule f I G U
  letI := formalGradedAffineModule_scalarTower_left f I F U
  letI := formalGradedAffineModule_scalarTower_left f I G U
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  letI : G.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct G.gradedPiece
  (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))))).map
      (formalGradedLocalMap f I φ U) ≫ (formalGradedLocalPushforwardIso f I G U).hom =
    (formalGradedLocalPushforwardIso f I F U).hom ≫
      (Scheme.Modules.restrictFunctor U.property.fromSpec).map
        (Limits.Sigma.map (fun n => F.gradedPieceMap φ n)) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule f I G U
  let := formalGradedAffineModule_scalarTower_left f I F U
  let := formalGradedAffineModule_scalarTower_left f I G U
  let : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  let : G.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct G.gradedPiece
  let a := (Scheme.Modules.restrictFunctor U.property.fromSpec).map
          (Limits.Sigma.map (fun n => F.gradedPieceMap φ n))
  let b := ModuleCat.ofHom (formalGradedAffineCoordinateMap f I U φ)
  let qF := (affineChartΓIso U F.gradedUnderlying ≪≫
    QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).hom
  let qG := (affineChartΓIso U G.gradedUnderlying ≪≫
    QuasiCoherent.affineOpenSectionsCoproductIso G.gradedPiece U).hom
  have hc := QuasiCoherent.affineOpenSectionsCoproductIso_inv_naturality
    F.gradedPiece G.gradedPiece (fun n => F.gradedPieceMap φ n) U
  have hc' : (Limits.Sigma.map (fun n => F.gradedPieceMap φ n)).val.app (op U.val) ≫
      (QuasiCoherent.affineOpenSectionsCoproductIso G.gradedPiece U).hom =
    (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).hom ≫ b := by
    apply (cancel_epi (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).inv).1
    rw [← Category.assoc, hc]
    change (b ≫ (QuasiCoherent.affineOpenSectionsCoproductIso G.gradedPiece U).inv) ≫
      (QuasiCoherent.affineOpenSectionsCoproductIso G.gradedPiece U).hom =
        (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).inv ≫
          (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).hom ≫ b
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have hq : moduleSpecΓFunctor.map a ≫ qG = qF ≫ b := by
    dsimp only [qF, qG, Iso.trans_hom]
    rw [← Category.assoc, affineChartΓIso_naturality]
    simp only [Category.assoc]
    rw [hc']
  have hchart := affineQuotientFromSections_naturality qF qG a b hq
  change a ≫ (formalGradedCoproductChartIso f I G U).hom =
    (formalGradedCoproductChartIso f I F U).hom ≫ tilde.map b at hchart
  let p := CommRingCat.ofHom (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))
  let b' := ModuleCat.ofHom (formalGradedAffineMap f I U φ)
  have hf : (ModuleCat.restrictScalars p.hom).map b' ≫
      (formalGradedLocalForgetIso f I G U).hom =
    (formalGradedLocalForgetIso f I F U).hom ≫ b := by
    ext x
    rfl
  have hp := (tildePushforwardIso p).hom.naturality b'
  dsimp only [Functor.comp_map] at hp
  apply (cancel_mono (formalGradedCoproductChartIso f I G U).hom).1
  change ((Scheme.Modules.pushforward (Spec.map p)).map (tilde.map b') ≫
    ((tildePushforwardIso p).hom.app (formalGradedLocalModule f I G U) ≫
      (tilde.functor Γ(X, U)).map (formalGradedLocalForgetIso f I G U).hom ≫
      (formalGradedCoproductChartIso f I G U).inv)) ≫
      (formalGradedCoproductChartIso f I G U).hom =
    (((tildePushforwardIso p).hom.app (formalGradedLocalModule f I F U) ≫
      (tilde.functor Γ(X, U)).map (formalGradedLocalForgetIso f I F U).hom ≫
      (formalGradedCoproductChartIso f I F U).inv) ≫ a) ≫
      (formalGradedCoproductChartIso f I G U).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hchart]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  erw [hp]
  simp only [Category.assoc]
  erw [← Functor.map_comp, hf, Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
