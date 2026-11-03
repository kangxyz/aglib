/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.SingleUnit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleUnit.ShortExact
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison.UnitIsIso

/-!
# Projection formula and the original structural unit

The original single units and original tensor unitors normalize the derived
projection formula. All arrows are the installed geometric adjunction arrows.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category instance for the original scheme module sheaves. -/
local instance structureUnitStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original right tensor unitor on actual pure tensor sections. -/
theorem tensorRightUnitIso_tmul (X : Scheme.{u}) (M : X.Modules) (U : X.Opensᵒᵖ)
    (m : M.val.obj U) (r : X.presheaf.obj U) :
    ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app M).val.app U
      ((tensorSheafUnit X M (SheafOfModules.unit X.ringCatSheaf)).app U (m ⊗ₜ r)) =
        r • m := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let : MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))
  let l := (MonoidalCategory.rightUnitor M.val).hom
  have h : tensorSheafUnit X M (SheafOfModules.unit X.ringCatSheaf) ≫
      ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app M).val = l := by
    change adj.homEquiv _ _ ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app M) = l
    have hl : (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app M =
        (adj.homEquiv _ _).symm l := (adj.homEquiv_counit _ _ l).symm
    rw [hl]
    exact (adj.homEquiv _ _).apply_symm_apply l
  exact congrArg (fun k ↦ k.app U (m ⊗ₜ r)) h

/-- The original tensor pushforward preserves the right structure unit, with
its original geometric adjunction unit on the other factor. -/
theorem pushforwardTensorMap_rightUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) :
    tensorSheafMap Y ((pullbackPushforwardAdjunction f).unit.app M)
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      pushforwardTensorMap f ((pullback f).obj M) (SheafOfModules.unit X.ringCatSheaf) ≫
      (pushforward f).map
        ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app
          ((pullback f).obj M)) =
    (SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).hom.app M ≫
      (pullbackPushforwardAdjunction f).unit.app M := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m r
  change M.val.obj U at m
  change Y.presheaf.obj U at r
  change ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app
      ((pullback f).obj M)).val.app (op (f ⁻¹ᵁ U.unop))
    ((pushforwardTensorMap f ((pullback f).obj M)
      (SheafOfModules.unit X.ringCatSheaf)).val.app U
      ((tensorSheafMap Y ((pullbackPushforwardAdjunction f).unit.app M)
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app U
          ((tensorSheafUnit Y M (SheafOfModules.unit Y.ringCatSheaf)).app U (m ⊗ₜ r)))) =
    ((pullbackPushforwardAdjunction f).unit.app M).val.app U
      (((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).hom.app M).val.app U
        ((tensorSheafUnit Y M (SheafOfModules.unit Y.ringCatSheaf)).app U (m ⊗ₜ r)))
  have h₁ := tensorSheafMap_tmul Y ((pullbackPushforwardAdjunction f).unit.app M)
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) U m r
  have h₂ := pushforwardTensorMap_tmul f ((pullback f).obj M)
    (SheafOfModules.unit X.ringCatSheaf) U
    (((pullbackPushforwardAdjunction f).unit.app M).val.app U m) (f.app U.unop r)
  have h₃ := tensorRightUnitIso_tmul X ((pullback f).obj M)
    (op (f ⁻¹ᵁ U.unop)) (((pullbackPushforwardAdjunction f).unit.app M).val.app U m)
    (f.app U.unop r)
  have h₄ := tensorRightUnitIso_tmul Y M U m r
  exact (congrArg (fun z ↦
      ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app
        ((pullback f).obj M)).val.app (op (f ⁻¹ᵁ U.unop)) z)
    ((congrArg (fun z ↦ (pushforwardTensorMap f ((pullback f).obj M)
      (SheafOfModules.unit X.ringCatSheaf)).val.app U z) h₁).trans h₂)).trans
    (h₃.trans
      (((((pullbackPushforwardAdjunction f).unit.app M).val.app U).hom.map_smul r m).symm.trans
      (congrArg (fun z ↦ ((pullbackPushforwardAdjunction f).unit.app M).val.app U z) h₄.symm)))

/-- The ordinary projection formula carries the actual structural unit to
 the actual adjunction unit on an arbitrary module coefficient. -/
theorem projectionFormulaMap_structureUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) :
    (moduleTensorLeftFunctor Y M).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      projectionFormulaMap f M (SheafOfModules.unit X.ringCatSheaf) ≫
      (pushforward f).map
        ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app
          ((pullback f).obj M)) =
    (SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).hom.app M ≫
      (pullbackPushforwardAdjunction f).unit.app M := by
  have hT : (moduleTensorLeftFunctor Y M).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
      tensorSheafMap Y (𝟙 M)
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
    simp only [moduleTensorLeftFunctor, SheafOfModulesOfCommRing.tensorLeftFunctor_map,
      tensorSheafMap, SheafOfModulesOfCommRing.tensorMap]
    erw [(SheafOfModulesOfCommRing.toPresheaf Y.sheaf).map_id]
  have hC : (moduleTensorCoefficientMap Y ((pullbackPushforwardAdjunction f).unit.app M)).app
      ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) =
      tensorSheafMap Y ((pullbackPushforwardAdjunction f).unit.app M) (𝟙 _) := by
    simp only [moduleTensorCoefficientMap, SheafOfModulesOfCommRing.tensorFunctor_map_app,
      tensorSheafMap, SheafOfModulesOfCommRing.tensorMap]
    erw [(SheafOfModulesOfCommRing.toPresheaf Y.sheaf).map_id]
  rw [hT, projectionFormulaMap, hC]
  simp only [Category.assoc]
  erw [tensorSheafMap_comp_assoc]
  erw [Category.id_comp, Category.comp_id]
  exact pushforwardTensorMap_rightUnit f M

/-- The actual single-unit square of the derived projection formula. -/
theorem derivedProjectionFormulaIso_singleUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [IsFiniteLocallyFree Y E] (M : X.Modules) :
    (moduleTensorLeftFunctor Y E).rightDerivedSingleUnit ((pushforward f).obj M) ≫
        (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlus.map
          ((pushforward f).rightDerivedSingleUnit M) ≫
        (derivedProjectionFormulaIso f E).hom.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) =
      (DerivedCategory.Plus.singleFunctor Y.Modules 0).map (projectionFormulaMap f E M) ≫
        (pushforward f).rightDerivedSingleUnit
          ((moduleTensorLeftFunctor X ((pullback f).obj E)).obj M) ≫
        (pushforward f).rightDerivedFunctorPlus.map
          ((moduleTensorLeftFunctor X ((pullback f).obj E)).rightDerivedSingleUnit M) := by
  let H := pushforward f
  let T := moduleTensorLeftFunctor Y E
  let S := moduleTensorLeftFunctor X ((pullback f).obj E)
  let : IsIso (Functor.rightDerivedFunctorPlusCompComparison H T) :=
    Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology H T
  let : (S.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorPlusCompUnit S H) (CochainComplex.Plus.quasiIso X.Modules) :=
    tensorPushforward_isRightDerived f E
  let : IsIso (Functor.rightDerivedFunctorPlusCompComparison S H) :=
    Functor.isIso_rightDerivedFunctorPlusCompComparison_of_isRightDerivedFunctor S H
  rw [← Functor.rightDerivedSingleUnit_comp_assoc]
  simp only [derivedProjectionFormulaIso, Functor.rightDerivedFunctorPlusThreeFactorIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightDerivedFunctorPlusCompIso, asIso_inv,
    NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, asIso_hom]
  rw [← Functor.rightDerivedSingleUnit_iso_hom_assoc,
    Functor.rightDerivedSingleUnit_comp, projectionFormulaNatIso_hom_app]

/-- Tensoring the original structural unit followed by any original section
retains the actual adjunction and positive-section insertion. -/
theorem derivedProjectionFormulaIso_sectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [IsFiniteLocallyFree Y E] (Q : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ Q) :
    let P := (pullback f).obj E
    let T := moduleTensorLeftFunctor Y E
    let S := moduleTensorLeftFunctor X P
    let H := pushforward f
    let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
    let SY := DerivedCategory.Plus.singleFunctor Y.Modules 0
    let RX : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅ P :=
      (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app P
    let RY := (SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app E
    let d : E ⟶ H.obj (S.obj Q) := (pullbackPushforwardAdjunction f).unit.app E ≫
      H.map (RX.inv ≫ tensorSheafMap X (𝟙 P) s)
    T.rightDerivedSingleUnit (SheafOfModules.unit Y.ringCatSheaf) ≫
        T.rightDerivedFunctorPlus.map
          (Scheme.Cohomology.moduleDerivedPushforwardUnit Y f ≫
            H.rightDerivedFunctorPlus.map (SX.map s)) ≫
        (derivedProjectionFormulaIso f E).hom.app (SX.obj Q) =
      SY.map RY.hom ≫ SY.map d ≫ H.rightDerivedSingleUnit (S.obj Q) ≫
        H.rightDerivedFunctorPlus.map (S.rightDerivedSingleUnit Q) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let P := (pullback f).obj E
  let T := moduleTensorLeftFunctor Y E
  let S := moduleTensorLeftFunctor X P
  let H := pushforward f
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let RX : S.obj OX ≅ P :=
    (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app P
  let RY := (SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app E
  let η := (pullbackPushforwardAdjunction f).unit.app E
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let w := u ≫ H.map s
  let d : E ⟶ H.obj (S.obj Q) := η ≫ H.map (RX.inv ≫ tensorSheafMap X (𝟙 P) s)
  let δ := Scheme.Cohomology.moduleDerivedPushforwardUnit Y f ≫
    H.rightDerivedFunctorPlus.map (SX.map s)
  have hS : S.map s = tensorSheafMap X (𝟙 P) s := by
    simp only [S, moduleTensorLeftFunctor, SheafOfModulesOfCommRing.tensorLeftFunctor_map,
      tensorSheafMap, SheafOfModulesOfCommRing.tensorMap]
    erw [(SheafOfModulesOfCommRing.toPresheaf X.sheaf).map_id]
  have hUnit : T.map u ≫ projectionFormulaMap f E OX ≫ H.map RX.hom =
      RY.hom ≫ η := projectionFormulaMap_structureUnit f E
  have hPost := congrArg (fun k => k ≫ H.map (RX.inv ≫ S.map s)) hUnit
  have hOrd : T.map w ≫ projectionFormulaMap f E Q = RY.hom ≫ d := by
    calc
      _ = T.map u ≫ projectionFormulaMap f E OX ≫ H.map (S.map s) := by
        dsimp only [w]
        rw [Functor.map_comp, Category.assoc, projectionFormulaMap_naturality]
      _ = _ := by
        simpa only [d, Category.assoc, ← H.map_comp, Iso.hom_inv_id_assoc, hS]
          using hPost
  have hδ : δ = SY.map w ≫ H.rightDerivedSingleUnit Q := by
    change (SY.map u ≫ H.rightDerivedSingleUnit OX) ≫
      H.rightDerivedFunctorPlus.map (SX.map s) = SY.map (u ≫ H.map s) ≫ _
    rw [Category.assoc, ← H.rightDerivedSingleUnit_naturality, ← SY.map_comp_assoc]
  change T.rightDerivedSingleUnit OY ≫ T.rightDerivedFunctorPlus.map δ ≫
      (derivedProjectionFormulaIso f E).hom.app (SX.obj Q) =
    SY.map RY.hom ≫ SY.map d ≫ H.rightDerivedSingleUnit (S.obj Q) ≫
      H.rightDerivedFunctorPlus.map (S.rightDerivedSingleUnit Q)
  calc
    _ = SY.map (T.map w) ≫ T.rightDerivedSingleUnit (H.obj Q) ≫
        T.rightDerivedFunctorPlus.map (H.rightDerivedSingleUnit Q) ≫
        (derivedProjectionFormulaIso f E).hom.app (SX.obj Q) := by
      rw [hδ, Functor.map_comp]
      simp only [Category.assoc]
      rw [← T.rightDerivedSingleUnit_naturality_assoc]
    _ = SY.map (T.map w) ≫ SY.map (projectionFormulaMap f E Q) ≫
        H.rightDerivedSingleUnit (S.obj Q) ≫
        H.rightDerivedFunctorPlus.map (S.rightDerivedSingleUnit Q) := by
      rw [derivedProjectionFormulaIso_singleUnit]
    _ = _ := by
      rw [← SY.map_comp_assoc, hOrd, SY.map_comp]
      simp only [Category.assoc]

/-- An isomorphism of the original derived structure unit implies an
isomorphism of the original adjunction unit on every finite locally free
coefficient. The proof uses the actual projection formula, not exactness of
ordinary global sections. -/
theorem isIso_derivedPullbackPushforwardUnit_of_structureUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules) [IsFiniteLocallyFree Y E]
    [IsIso (Scheme.Cohomology.moduleDerivedPushforwardUnit Y f)] :
    IsIso ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map
        ((pullbackPushforwardAdjunction f).unit.app E) ≫
      (pushforward f).rightDerivedSingleUnit ((pullback f).obj E)) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let H := pushforward f
  let T := moduleTensorLeftFunctor Y E
  let S := moduleTensorLeftFunctor X ((pullback f).obj E)
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let RX : S.obj OX ≅ (pullback f).obj E :=
    (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app ((pullback f).obj E)
  let RY : T.obj OY ≅ E := (SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app E
  let η := (pullbackPushforwardAdjunction f).unit.app E
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let U := SY.map η ≫ H.rightDerivedSingleUnit ((pullback f).obj E)
  let : IsIso T.rightDerivedFunctorPlusUnit := isIso_moduleTensorLeft_derivedUnit E
  let : IsIso S.rightDerivedFunctorPlusUnit :=
    isIso_moduleTensorLeft_derivedUnit ((pullback f).obj E)
  have hT : IsIso (T.rightDerivedSingleUnit OY) :=
    T.isIso_rightDerivedSingleUnit_of_isIso_unit OY
  have hS : IsIso (S.rightDerivedSingleUnit OX) :=
    S.isIso_rightDerivedSingleUnit_of_isIso_unit OX
  let := hT
  let := hS
  have hOrd : T.map u ≫ projectionFormulaMap f E OX =
      RY.hom ≫ η ≫ H.map RX.inv := by
    apply (cancel_mono (H.map RX.hom)).mp
    simp only [Category.assoc, ← H.map_comp, Iso.inv_hom_id]
    exact projectionFormulaMap_structureUnit f E
  have hNorm : T.rightDerivedSingleUnit OY ≫
      T.rightDerivedFunctorPlus.map (Scheme.Cohomology.moduleDerivedPushforwardUnit Y f) ≫
      (derivedProjectionFormulaIso f E).hom.app (SX.obj OX) =
      SY.map RY.hom ≫ U ≫
        H.rightDerivedFunctorPlus.map (SX.map RX.inv ≫ S.rightDerivedSingleUnit OX) := by
    dsimp only [Scheme.Cohomology.moduleDerivedPushforwardUnit]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.rightDerivedSingleUnit_naturality_assoc]
    erw [derivedProjectionFormulaIso_singleUnit]
    rw [← Functor.map_comp_assoc, hOrd]
    simp only [Functor.map_comp, Category.assoc, U]
    have hn := H.rightDerivedSingleUnit_naturality RX.inv
    have hp := congrArg (fun z => SY.map RY.hom ≫ SY.map η ≫ z ≫
      H.rightDerivedFunctorPlus.map (S.rightDerivedSingleUnit OX)) hn
    simp only [Category.assoc] at hp
    dsimp only [SX, SY, S, H, T, OX, OY] at hp ⊢
    exact hp
  have hIso : IsIso (SY.map RY.hom ≫ U ≫
      H.rightDerivedFunctorPlus.map (SX.map RX.inv ≫ S.rightDerivedSingleUnit OX)) := by
    rw [← hNorm]
    infer_instance
  let := hIso
  have hU : IsIso U := by
    have : IsIso (U ≫ H.rightDerivedFunctorPlus.map
        (SX.map RX.inv ≫ S.rightDerivedSingleUnit OX)) :=
      (isIso_comp_left_iff _ _).mp hIso
    exact (isIso_comp_right_iff U (H.rightDerivedFunctorPlus.map
      (SX.map RX.inv ≫ S.rightDerivedSingleUnit OX))).mp inferInstance
  exact hU

end AlgebraicGeometry.Scheme.Modules
