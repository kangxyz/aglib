/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsOpenEnlargement
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections

/-! # Original finite locally free restriction over a Hartogs open

The original structure-module unit and ordinary projection formula control the
original geometric adjunction unit for finite locally free coefficients. The
bundle is only defined on the larger open; no extension to the ambient affine
scheme is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Insert the original structure-unit in the second tensor factor. -/
def structureUnitTensorInsertion {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    M ⟶ (moduleTensorLeftFunctor Y M).obj
      ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app M).inv ≫
    (moduleTensorLeftFunctor Y M).map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

/-- The insertion is the original pure section tensor with one. -/
theorem structureUnitTensorInsertion_section
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) :
    Hom.app (structureUnitTensorInsertion f M) U m =
      moduleTensorSection Y M ((pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) U m (1 : Γ(X, f ⁻¹ᵁ U)) := by
  change ((moduleTensorLeftFunctor Y M).map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app (op U)
      (((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app M).inv.val.app (op U) m) = _
  rw [show ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app M).inv.val.app (op U) m =
      moduleTensorSection Y M (SheafOfModules.unit Y.ringCatSheaf) U m (1 : Γ(Y, U)) from
        rightUnitor_inv_moduleTensorSection M U m]
  erw [moduleTensorLeftFunctor_map_section]
  congr 1
  exact map_one (f.app U).hom

/-- The original projection formula followed by its original right unitor. -/
def projectionFormulaUnitMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (moduleTensorLeftFunctor Y M).obj
      ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ⟶
        (pushforward f).obj ((pullback f).obj M) :=
  projectionFormulaMap f M (SheafOfModules.unit X.ringCatSheaf) ≫
    (pushforward f).map
      ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app ((pullback f).obj M)).hom

/-- The original projection/unit map acts on pure section tensors by the
geometric unit and the original scalar action. -/
theorem projectionFormulaUnitMap_section
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) (a : Γ(X, f ⁻¹ᵁ U)) :
    Hom.app (projectionFormulaUnitMap f M) U
      (moduleTensorSection Y M ((pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) U m a) =
      a • (show Γ((pullback f).obj M, f ⁻¹ᵁ U) from
        Hom.app ((pullbackPushforwardAdjunction f).unit.app M) U m) := by
  change ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app
    ((pullback f).obj M)).hom.val.app (op (f ⁻¹ᵁ U))
    (Hom.app (projectionFormulaMap f M (SheafOfModules.unit X.ringCatSheaf)) U
      (moduleTensorSection Y M ((pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) U m a)) = _
  rw [projectionFormulaMap_section]
  exact tensorRightUnitIso_hom_section X ((pullback f).obj M) (f ⁻¹ᵁ U) _ a

/-- These native tensor constructions factor the original geometric unit. -/
theorem projectionFormula_structureUnit_factorization
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    structureUnitTensorInsertion f M ≫ projectionFormulaUnitMap f M =
      (pullbackPushforwardAdjunction f).unit.app M := by
  apply hom_ext
  intro U
  ext m
  change Hom.app (projectionFormulaUnitMap f M) U
    (Hom.app (structureUnitTensorInsertion f M) U m) = _
  rw [structureUnitTensorInsertion_section, projectionFormulaUnitMap_section, one_smul]
  rfl

/-- An actual structure-unit isomorphism implies the actual adjunction unit
is an isomorphism for every finite locally free coefficient. -/
theorem isIso_pullbackUnit_of_structureUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)]
    (M : Y.Modules) [IsFiniteLocallyFree Y M] :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  let : IsIso (projectionFormulaMap f M (SheafOfModules.unit X.ringCatSheaf)) :=
    isIso_projectionFormulaMap f M _
  have hi : IsIso (structureUnitTensorInsertion f M) := by
    dsimp only [structureUnitTensorInsertion]
    infer_instance
  have hp : IsIso (projectionFormulaUnitMap f M) := by
    dsimp only [projectionFormulaUnitMap]
    infer_instance
  rw [← projectionFormula_structureUnit_factorization f M]
  infer_instance

/-- For an open immersion the statement concerns the original restriction
unit, not an independently chosen pullback identification. -/
theorem isIso_restrictUnit_of_structureUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)]
    (M : Y.Modules) [IsFiniteLocallyFree Y M] :
    IsIso ((restrictAdjunction f).unit.app M) := by
  let : IsIso ((pullbackPushforwardAdjunction f).unit.app M) :=
    isIso_pullbackUnit_of_structureUnit f M
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction f) (pullbackPushforwardAdjunction f) M
  have hi : IsIso ((restrictAdjunction f).unit.app M ≫
      (pushforward f).map ((restrictFunctorIsoPullback f).hom.app M)) := by
    rw [show (restrictAdjunction f).unit.app M ≫
      (pushforward f).map ((restrictFunctorIsoPullback f).hom.app M) =
      (pullbackPushforwardAdjunction f).unit.app M from h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((pushforward f).map
    ((restrictFunctorIsoPullback f).hom.app M))

/-- The original structure-unit on the actual inclusion of the smaller
Hartogs open into a larger open is an isomorphism. -/
theorem isIso_structureUnit_homOfLE_hartogs
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] [QuasiCompact V.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (Scheme.affineScalarMap U.ι)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
      ((Spec (.of A)).homOfLE hUV).toRingCatSheafHom) := by
  let j := (Spec (.of A)).homOfLE hUV
  have hV := Scheme.affineScalarMap_bijective_of_hartogs_open_le A U V hUV hU
  let : IsIso (SheafOfModules.unitToPushforwardObjUnit U.ι.toRingCatSheafHom) :=
    Scheme.isIso_unitToPushforward_of_hartogs_open A U hU
  let : IsIso (SheafOfModules.unitToPushforwardObjUnit V.ι.toRingCatSheafHom) :=
    Scheme.isIso_unitToPushforward_of_hartogs_open A V hV
  have hc := unitToPushforwardObjUnit_comp j V.ι
  have hj : j ≫ V.ι = U.ι := by simp [j]
  let : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (j ≫ V.ι).toRingCatSheafHom) := by
    rw [hj]
    infer_instance
  have ht : IsIso
      (SheafOfModules.unitToPushforwardObjUnit V.ι.toRingCatSheafHom ≫
        (pushforward V.ι).map
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
        (pushforwardComp j V.ι).hom.app
          (SheafOfModules.unit U.toScheme.ringCatSheaf)) := by
    rw [hc]
    infer_instance
  let : IsIso ((pushforward V.ι).map
      (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)) := by
    let : IsIso ((pushforward V.ι).map
        (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
          (pushforwardComp j V.ι).hom.app
            (SheafOfModules.unit U.toScheme.ringCatSheaf)) :=
      IsIso.of_isIso_comp_left
        (SheafOfModules.unitToPushforwardObjUnit V.ι.toRingCatSheafHom) _
    exact IsIso.of_isIso_comp_right _ ((pushforwardComp j V.ι).hom.app
      (SheafOfModules.unit U.toScheme.ringCatSheaf))
  let : (pushforward V.ι).Full := (restrictAdjunction V.ι).fullyFaithfulROfIsIsoCounit.full
  let : (pushforward V.ι).Faithful := (restrictAdjunction V.ι).fullyFaithfulROfIsIsoCounit.faithful
  exact isIso_of_reflects_iso _ (pushforward V.ι)

/-- The original restriction-unit map on sections is bijective for a bundle
on V itself, without choosing an extension of that bundle to Spec A. -/
theorem finiteLocallyFree_hartogs_restriction_bijective
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] [QuasiCompact V.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (Scheme.affineScalarMap U.ι))
    (M : V.toScheme.Modules) [IsFiniteLocallyFree V M]
    (T : V.toScheme.Opens) :
    Function.Bijective
      (Hom.app ((restrictAdjunction ((Spec (.of A)).homOfLE hUV)).unit.app M) T) := by
  let j := (Spec (.of A)).homOfLE hUV
  let : IsIso (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) :=
    isIso_structureUnit_homOfLE_hartogs A U V hUV hU
  let : IsIso ((restrictAdjunction j).unit.app M) :=
    isIso_restrictUnit_of_structureUnit j M
  exact (ConcreteCategory.isIso_iff_bijective
    (Hom.app ((restrictAdjunction j).unit.app M) T)).mp inferInstance

end AlgebraicGeometry.Scheme.Modules
