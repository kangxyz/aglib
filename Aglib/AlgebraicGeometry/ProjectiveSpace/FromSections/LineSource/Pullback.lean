/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource.Naturality
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Original line-source projective coordinates in a pulled source frame

The canonical tensor pullback comparison and the pulled original dual
evaluation construct the coefficient isomorphism for a specified frame
of the pulled source line. Each original pulled coordinate becomes the
original pulled morphism evaluated in that frame. The corresponding
projective scheme morphisms are equal over the original affine base.

No comparison between a pulled dual and a newly chosen dual is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource

variable {X T : Scheme.{u}} (g : T ⟶ X) (D : X.Modules) (hD : IsLocallyRankOne X D)

/-- The canonical actual tensor comparison with the original pulled dual factor. -/
def pulledDualTensorIso (J : X.Modules) :
    (Scheme.Modules.pullback g).obj (coefficientModule D J) ≅
      tensorSheaf T ((Scheme.Modules.pullback g).obj (dualSheaf X D))
        ((Scheme.Modules.pullback g).obj J) := by
  let : IsIso (pullbackTensorMap g (dualSheaf X D) J) :=
    PullbackTensor.Local.pullbackTensorMap_isIso g (dualSheaf X D) J
      (dualSheaf_locallyRankOne X D hD)
  exact asIso (pullbackTensorMap g (dualSheaf X D) J)

/-- Pull the original dual evaluation through the actual tensor and unit comparisons. -/
def pulledEvaluationIso :
    tensorSheaf T ((Scheme.Modules.pullback g).obj (dualSheaf X D))
      ((Scheme.Modules.pullback g).obj D) ≅ SheafOfModules.unit T.ringCatSheaf :=
  (pulledDualTensorIso g D hD D).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (dualEvaluationIso X ⟨D, hD⟩) ≪≫
      pullbackUnitIso g

variable (eD : (Scheme.Modules.pullback g).obj D ≅ SheafOfModules.unit T.ringCatSheaf)

/-- The supplied frame and pulled evaluation trivialize the original pulled dual factor. -/
def pulledDualFrame :
    (Scheme.Modules.pullback g).obj (dualSheaf X D) ≅ SheafOfModules.unit T.ringCatSheaf :=
  (MonoidalCategory.rightUnitor (C := T.Modules)
      ((Scheme.Modules.pullback g).obj (dualSheaf X D))).symm ≪≫
    (tensorLeft (C := T.Modules)
      ((Scheme.Modules.pullback g).obj (dualSheaf X D))).mapIso eD.symm ≪≫
        pulledEvaluationIso g D hD

/-- The actual trivialized coefficient tensor functor on the new source. -/
def pulledCoefficientNatIso :
    tensorLeft (C := T.Modules) ((Scheme.Modules.pullback g).obj (dualSheaf X D)) ≅
      𝟭 T.Modules :=
  (tensoringLeft T.Modules).mapIso (pulledDualFrame g D hD eD) ≪≫
    leftUnitorNatIso T.Modules

/-- At the unit, the coefficient comparison retains the supplied inverse frame. -/
theorem pulledCoefficientNatIso_unit :
    (pulledCoefficientNatIso g D hD eD).hom.app (SheafOfModules.unit T.ringCatSheaf) =
      (tensorLeft (C := T.Modules)
        ((Scheme.Modules.pullback g).obj (dualSheaf X D))).map eD.inv ≫
          (pulledEvaluationIso g D hD).hom := by
  change MonoidalCategory.whiskerRight (C := T.Modules)
      (pulledDualFrame g D hD eD).hom (𝟙_ T.Modules) ≫
        (MonoidalCategory.leftUnitor (C := T.Modules) (𝟙_ T.Modules)).hom = _
  rw [unitors_equal, rightUnitor_naturality]
  simp only [pulledDualFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]

/-- At the pulled source, the comparison is the original evaluation and inverse frame. -/
theorem pulledCoefficientNatIso_source :
    (pulledCoefficientNatIso g D hD eD).hom.app ((Scheme.Modules.pullback g).obj D) =
      (pulledEvaluationIso g D hD).hom ≫ eD.inv := by
  apply (cancel_epi ((tensorLeft (C := T.Modules)
    ((Scheme.Modules.pullback g).obj (dualSheaf X D))).map eD.inv)).mp
  rw [(pulledCoefficientNatIso g D hD eD).hom.naturality eD.inv,
    pulledCoefficientNatIso_unit]
  rfl

/-- The actual pulled coefficient module identified using the supplied pulled source frame. -/
def pulledCoefficientIso (J : X.Modules) :
    (Scheme.Modules.pullback g).obj (coefficientModule D J) ≅
      (Scheme.Modules.pullback g).obj J :=
  pulledDualTensorIso g D hD J ≪≫
    (pulledCoefficientNatIso g D hD eD).app ((Scheme.Modules.pullback g).obj J)

/-- Every original pulled coordinate is exactly the pulled morphism in the supplied frame. -/
theorem pulledSection_trivialized (J : X.Modules) (d : D ⟶ J) :
    pullbackSection g (sectionOfHom D J hD d) ≫
      (pulledCoefficientIso g D hD eD J).hom =
        eD.inv ≫ (Scheme.Modules.pullback g).map d := by
  have hn : (Scheme.Modules.pullback g).map
      ((tensorLeft (C := X.Modules) (dualSheaf X D)).map d) ≫
        (pulledDualTensorIso g D hD J).hom =
      (pulledDualTensorIso g D hD D).hom ≫
        (tensorLeft (C := T.Modules)
          ((Scheme.Modules.pullback g).obj (dualSheaf X D))).map
            ((Scheme.Modules.pullback g).map d) := by
    calc
      _ = (Scheme.Modules.pullback g).map (tensorSheafMap X (𝟙 (dualSheaf X D)) d) ≫
          pullbackTensorMap g (dualSheaf X D) J :=
        congrArg (fun k => (Scheme.Modules.pullback g).map k ≫
          pullbackTensorMap g (dualSheaf X D) J)
          (whiskerLeft_eq_tensorSheafMap X (dualSheaf X D) d)
      _ = pullbackTensorMap g (dualSheaf X D) D ≫
          tensorSheafMap T ((Scheme.Modules.pullback g).map (𝟙 (dualSheaf X D)))
            ((Scheme.Modules.pullback g).map d) :=
        pullbackTensorMap_naturality g (𝟙 (dualSheaf X D)) d
      _ = _ :=
        (congrArg (fun k => pullbackTensorMap g (dualSheaf X D) D ≫
          tensorSheafMap T k ((Scheme.Modules.pullback g).map d))
          ((Scheme.Modules.pullback g).map_id (dualSheaf X D))).trans
            (congrArg (fun k => pullbackTensorMap g (dualSheaf X D) D ≫ k)
              (whiskerLeft_eq_tensorSheafMap T
                ((Scheme.Modules.pullback g).obj (dualSheaf X D))
                ((Scheme.Modules.pullback g).map d)).symm)
  change ((pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map
        ((dualEvaluationIso X ⟨D, hD⟩).inv ≫
          (tensorLeft (C := X.Modules) (dualSheaf X D)).map d)) ≫
        ((pulledDualTensorIso g D hD J).hom ≫
          (pulledCoefficientNatIso g D hD eD).hom.app
            ((Scheme.Modules.pullback g).obj J)) = _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, (pulledCoefficientNatIso g D hD eD).hom.naturality,
    pulledCoefficientNatIso_source]
  simp only [pulledEvaluationIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.id_map, Category.assoc]
  rw [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  exact (congrArg (fun k :
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf) =>
      (pullbackUnitIso g).inv ≫ k ≫ (pullbackUnitIso g).hom ≫
        eD.inv ≫ (Scheme.Modules.pullback g).map d)
      ((Scheme.Modules.pullback g).map_id (SheafOfModules.unit X.ringCatSheaf))).trans
    ((congrArg (fun k => (pullbackUnitIso g).inv ≫ k)
      (Category.id_comp ((pullbackUnitIso g).hom ≫
        eD.inv ≫ (Scheme.Modules.pullback g).map d))).trans
      (Iso.inv_hom_id_assoc (pullbackUnitIso g)
        (eD.inv ≫ (Scheme.Modules.pullback g).map d)))

variable (J : X.Modules) {ι : Type u} (d : ι → (D ⟶ J)) [Epi (Sigma.desc d)]

/-- Pulling the original row and using the supplied source frame preserves generation. -/
instance pulledTrivializedFamily_epi :
    Epi (Sigma.desc (fun i => eD.inv ≫ (Scheme.Modules.pullback g).map (d i))) := by
  let F := Scheme.Modules.pullback g
  let : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction g)
  let : Epi (F.map (Sigma.desc d)) := F.map_epi (Sigma.desc d)
  let : Epi (Sigma.desc (fun i => F.map (d i))) := by
    rw [← sigmaComparison_map_desc F (fun _ : ι => D) J d]
    infer_instance
  exact trivializedFamily_epi (F.obj D) eD (F.obj J) (fun i => F.map (d i))

/-- The original projective morphism restricts to the original pulled row in its supplied frame. -/
theorem mapOfFamily_pullback_eq_of_sourceIso {R : Type u} [CommRing R] [Finite ι]
    (p : X ⟶ Spec (.of R)) (hJ : IsLocallyRankOne X J) :
    letI := pulledTrivializedFamily_epi g D eD J d
    g ≫ mapOfFamily D J hD p hJ d =
      mapOfFiniteFamily (g ≫ p) ((Scheme.Modules.pullback g).obj J)
        (pullback_locallyRankOne g J hJ)
        (fun i => eD.inv ≫ (Scheme.Modules.pullback g).map (d i)) := by
  let : Epi (Sigma.desc (fun i => eD.inv ≫ (Scheme.Modules.pullback g).map (d i))) :=
    pulledTrivializedFamily_epi g D eD J d
  unfold mapOfFamily
  have h := mapOfFiniteFamily_pullback_iso g p (coefficientModule D J)
    (coefficientModule_locallyRankOne D J hD hJ)
    (fun i => sectionOfHom D J hD (d i)) ((Scheme.Modules.pullback g).obj J)
    (pulledCoefficientIso g D hD eD J)
  simpa only [pulledFamily, pulledSection_trivialized] using h

end AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource
