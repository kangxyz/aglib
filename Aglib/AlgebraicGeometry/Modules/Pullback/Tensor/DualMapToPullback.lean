/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.PairingEquiv
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.TransposeEvaluation

/-!
# The original dual map into a pulled-back dual line

For an arbitrary map from the pullback of a line into an arbitrary module,
the existing perfect-pairing equivalence constructs the reverse map on duals.
Its whole pairing formula and transpose-section law retain the original
maps, evaluation and structural unit. The local module need not be a line.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (I : LineBundle X) (J : Y.Modules)
  (e : (pullback f).obj I.val ⟶ J)

/-- The existing inverse pairing equivalence sends the original dual of J
into the pullback of the original dual line, without inverting e. -/
def dualMapToPullback :
    (show Y.Modules from dualSheaf Y J) ⟶ (pullback f).obj (dualLineBundle X I).val := by
  let ε :
      (show X.Modules from tensorSheaf X (dualLineBundle X I).val I.val) ≅
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
    dualEvaluationIso X I
  let : IsIso ε.hom := ε.isIso_hom
  exact (pullbackPairingOfEquiv f ε.hom I.property
    (show Y.Modules from dualSheaf Y J)).symm
      (tensorSheafMap Y (𝟙 (dualSheaf Y J)) e ≫
        evaluationSheaf Y J (SheafOfModules.unit Y.ringCatSheaf))

/-- The complete pairing formula for the same original dual-to-pullback map. -/
theorem dualMapToPullback_pairing :
    pullbackPairingOf f (dualEvaluationIso X I).hom (dualMapToPullback f I J e) =
      tensorSheafMap Y (𝟙 (dualSheaf Y J)) e ≫
        evaluationSheaf Y J (SheafOfModules.unit Y.ringCatSheaf) := by
  let ε :
      (show X.Modules from tensorSheaf X (dualLineBundle X I).val I.val) ≅
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
    dualEvaluationIso X I
  let : IsIso ε.hom := ε.isIso_hom
  exact (pullbackPairingOfEquiv f ε.hom I.property
    (show Y.Modules from dualSheaf Y J)).apply_symm_apply _

/-- An original coefficient square gives the original transpose-section law.
No line, quasicoherence, or finite-presentation hypothesis is placed on J. -/
theorem transpose_dualMapToPullback
    (α : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (β : J ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (h : e ≫ β = (pullback f).map α ≫ (pullbackUnitIso f).hom) :
    InternalHom.transpose Y β ≫ dualMapToPullback f I J e =
      (pullbackUnitIso f).inv ≫ (pullback f).map (InternalHom.transpose X α) := by
  let ε :
      (show X.Modules from tensorSheaf X (dualLineBundle X I).val I.val) ≅
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
    dualEvaluationIso X I
  let : IsIso ε.hom := ε.isIso_hom
  have ht :
      tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 ((pullback f).obj I.val)) ≫
          tensorSheafMap Y (𝟙 (dualSheaf Y J)) e =
        tensorSheafMap Y (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e ≫
          tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 J) := by
    have hleft := tensorSheafMap_comp Y
      (InternalHom.transpose Y β) (𝟙 ((pullback f).obj I.val)) (𝟙 (dualSheaf Y J)) e
    have hright := tensorSheafMap_comp Y
      (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e (InternalHom.transpose Y β) (𝟙 J)
    exact (hleft.trans (congrArg₂ (tensorSheafMap Y)
      (Category.comp_id (InternalHom.transpose Y β)) (Category.id_comp e))).trans
        (hright.trans (congrArg₂ (tensorSheafMap Y)
          (Category.id_comp (InternalHom.transpose Y β)) (Category.comp_id e))).symm
  have hu :
      tensorSheafMap Y (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e ≫
          (tensorSheafLeftUnit Y J).hom =
        (tensorSheafLeftUnit Y ((pullback f).obj I.val)).hom ≫ e :=
    MonoidalCategory.leftUnitor_naturality e
  let U : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let T : Y.Modules := tensorSheaf Y U ((pullback f).obj I.val)
  have hp :
      (show T ⟶ U from pullbackPairingOf f ε.hom
        (InternalHom.transpose Y β ≫ dualMapToPullback f I J e)) =
      (show T ⟶ U from pullbackPairingOf f ε.hom
        ((pullbackUnitIso f).inv ≫ (pullback f).map (InternalHom.transpose X α))) := by
    calc
      (show T ⟶ U from pullbackPairingOf f ε.hom
          (InternalHom.transpose Y β ≫ dualMapToPullback f I J e)) =
        (show T ⟶ U from tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 ((pullback f).obj I.val)) ≫
            pullbackPairingOf f ε.hom (dualMapToPullback f I J e)) :=
        pullbackPairingOf_comp f ε.hom _ _
      _ = (show T ⟶ U from
          tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 ((pullback f).obj I.val)) ≫
          (tensorSheafMap Y (𝟙 (dualSheaf Y J)) e ≫
            evaluationSheaf Y J (SheafOfModules.unit Y.ringCatSheaf))) :=
        congrArg (fun v :
          (show Y.Modules from tensorSheaf Y (dualSheaf Y J) ((pullback f).obj I.val)) ⟶ U =>
            tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 ((pullback f).obj I.val)) ≫ v)
          (dualMapToPullback_pairing f I J e)
      _ = (show T ⟶ U from
          (tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 ((pullback f).obj I.val)) ≫
          tensorSheafMap Y (𝟙 (dualSheaf Y J)) e) ≫
            evaluationSheaf Y J (SheafOfModules.unit Y.ringCatSheaf)) :=
        (Category.assoc _ _ _).symm
      _ = (show T ⟶ U from
          (tensorSheafMap Y (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e ≫
          tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 J)) ≫
            evaluationSheaf Y J (SheafOfModules.unit Y.ringCatSheaf)) :=
        congrArg (fun v : T ⟶ (show Y.Modules from tensorSheaf Y (dualSheaf Y J) J) =>
          v ≫ evaluationSheaf Y J (SheafOfModules.unit Y.ringCatSheaf)) ht
      _ = (show T ⟶ U from
          tensorSheafMap Y (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e ≫
          (tensorSheafMap Y (InternalHom.transpose Y β) (𝟙 J) ≫
            evaluationSheaf Y J (SheafOfModules.unit Y.ringCatSheaf))) :=
        Category.assoc _ _ _
      _ = (show T ⟶ U from
          tensorSheafMap Y (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e ≫
          ((tensorSheafLeftUnit Y J).hom ≫ β)) :=
        congrArg (fun v : (show Y.Modules from tensorSheaf Y U J) ⟶ U =>
          tensorSheafMap Y (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e ≫ v)
            (InternalHom.transpose_evaluation Y β)
      _ = (show T ⟶ U from
          (tensorSheafMap Y (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) e ≫
          (tensorSheafLeftUnit Y J).hom) ≫ β) :=
        (Category.assoc _ _ _).symm
      _ = (show T ⟶ U from
          ((tensorSheafLeftUnit Y ((pullback f).obj I.val)).hom ≫ e) ≫ β) :=
        congrArg (fun v : T ⟶ J => v ≫ β) hu
      _ = (show T ⟶ U from
          (tensorSheafLeftUnit Y ((pullback f).obj I.val)).hom ≫ (e ≫ β)) :=
        Category.assoc _ _ _
      _ = (show T ⟶ U from
          (tensorSheafLeftUnit Y ((pullback f).obj I.val)).hom ≫
          ((pullback f).map α ≫ (pullbackUnitIso f).hom)) :=
        congrArg (fun v : (pullback f).obj I.val ⟶ U =>
          (tensorSheafLeftUnit Y ((pullback f).obj I.val)).hom ≫ v) h
      _ = (show T ⟶ U from
          pullbackPairingOf f ε.hom
          ((pullbackUnitIso f).inv ≫ (pullback f).map (InternalHom.transpose X α))) :=
        (pullback_transpose_dualEvaluation f I α).symm
  exact (bijective_pullbackPairingOf f ε.hom I.property U).1 hp

end AlgebraicGeometry.Scheme.Modules
