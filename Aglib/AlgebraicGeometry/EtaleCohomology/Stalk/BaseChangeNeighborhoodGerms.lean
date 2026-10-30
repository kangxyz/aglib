/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartExchangeMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartRelative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeSectionComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductBaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeGlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.CategoryTheory.Sites.Point.SectionValuesTransport

/-! # Original higher exchange on arbitrary pointed neighborhood classes

Literal chart normalization and original global exchange give the section
equation after the target chart exchange. The target chart is etale, so its
original higher exchange can be cancelled. Taking the original germs then
gives the arbitrary-neighborhood equality with the original stalk unit,
pulled-back point and cohomology transfer.

The two chart cohomology groups use the common Ext universe required by
`Continuity.cohomologyTransfer`. The original and slice Ext universes and all
eight derived models remain independent. No Cartesian, properness or torsion
hypothesis is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OriginalSectionValues

universe u w w' s s' e dX dS dX' dS' dZU dU dZV dV

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge


section ChartNormalization

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
  [hOriginalExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The original resolution edge on represented cohomology as an additive map. -/
def originalCohomologySectionHom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      X.smallEtaleTopology F q ((siteBaseChange f).obj U) →+
        ((higherDirectImage f q).obj F).obj.obj (op U) :=
  representedSectionHomOfEquiv
    (((resolutionCohomologyToHigherDirectImage f q).app F).app (op U))
    (originalCohomologyResolutionEquiv f U F q)

variable
  [hSliceExt : HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})]
  [hChart : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance neighborhoodChartNormalization_chartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hChart

local instance neighborhoodChartNormalization_chartSiteExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj U).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hChart

/-- The original resolution edge and original class comparisons as one additive map. -/
def fibreProductCohomologySectionHom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q →+
      ((higherDirectImage f q).obj F).obj.obj (op U) :=
  (originalCohomologySectionHom f U F q).comp
    (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
      hOriginalExt hSliceExt hChart F q).symm.toAddMonoidHom

/-- The section hom is exactly the original edge, resolution comparison and inverse
fibre-product class comparison, with their original additive structures. -/
theorem fibreProductCohomologySectionHom_eq_original
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductCohomologySectionHom.{u, w, s, e} f U F q =
      ((((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)).hom.comp
        (originalCohomologyResolutionEquiv f U F q).toAddMonoidHom).comp
          (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
            hOriginalExt hSliceExt hChart F q).symm.toAddMonoidHom := rfl

private theorem fibreProductGerm_eq_sectionHom
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (p : (pointSmallEtale η).fiber.obj U) :
    fibreProductCohomologyGerm.{u, w, s, e} f U F q η p =
      ((pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f q).obj F).obj).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) := rfl

variable
  [hSourceDerived : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hTargetDerived : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hChartDerived : HasDerivedCategory.{dZU} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hBase : HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]

private theorem originalChartSection_hom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q).hom.comp
        (originalCohomologySectionHom f U F q) =
      (cohomologyToHigherSections (pullback.fst U.hom f)
        ((inverseImage (pullback.snd U.hom f)).obj F) q).comp
          (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
            hOriginalExt hSliceExt hChart F q).toAddMonoidHom := by
  apply addHom_eq_of_apply
  intro x
  simp only [AddMonoidHom.comp_apply]
  rw [fibreProductChartSectionMap_eq_constructor.{u, dX, dS, dZU, dU} f U
    (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
    (hChartDerived := hChartDerived) (hBase := hBase) F q]
  exact DFunLike.congr_fun (chartSectionHom_of_whole_values
    (@higherDirectImage.{u} X S f q)
    (@inverseImage.{u} X (pullback U.hom f) (pullback.snd U.hom f))
    (higherDirectImage (pullback.fst U.hom f) q)
    (@inverseImage.{u} S U.left U.hom) (globalSections U.left)
    (@higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
      hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
      U.hom (pullback.snd U.hom f) pullback.condition q)
    (higherBaseChangeMap f (pullback.fst U.hom f) U.hom
      (pullback.snd U.hom f) pullback.condition q)
    (@higherBaseChangeMapFromDerived_eq.{u, dX, dS, dZU, dU}
      X S (pullback U.hom f) U.left hSourceDerived hTargetDerived hChartDerived hBase
      f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f) pullback.condition q) F
    (Continuity.pullbackSectionsEtaleEvaluationIso ((higherDirectImage f q).obj F) U)
    (originalCohomologySectionHom f U F q)
    (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U
      hOriginalExt hSliceExt hChart F q)
    (cohomologyToHigherSections (pullback.fst U.hom f)
      ((inverseImage (pullback.snd U.hom f)).obj F) q)
    (@higherBaseChangeMap_originalChart.{u, w, s, e}
      X S f U hOriginalExt hSliceExt hChart F q)) x

private theorem fibreProductChartSection_hom (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) =
      cohomologyToHigherSections (pullback.fst U.hom f)
        ((inverseImage (pullback.snd U.hom f)).obj F) q :=
  chartHom_normalize
    (@fibreProductCohomologyEquiv.{u, w, s, e} X S f U hOriginalExt hSliceExt hChart F q)
    (originalCohomologySectionHom f U F q)
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q).hom
    (cohomologyToHigherSections (pullback.fst U.hom f)
      ((inverseImage (pullback.snd U.hom f)).obj F) q)
    (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) rfl
    (originalChartSection_hom.{u, w, s, e, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q)

end ChartNormalization

private theorem higherBaseChangeMap_coefficientSections_hom
    {X S Y T : Scheme.{u}}
    [hDomainExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [hCodomainExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    [hDomainDerived : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [hDomainBaseDerived : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [hCodomainDerived : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} Y)]
    [hCodomainBaseDerived : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} T)]
    (f : X ⟶ S) (fT : Y ⟶ T) (b : T ⟶ S) (r : Y ⟶ X)
    (h : fT ≫ b = r ≫ f) (F : AbelianSheaf.{u, u + 1} X)
    (G : AbelianSheaf.{u, u + 1} Y) (φ : (inverseImage r).obj F ⟶ G) (q : ℕ) :
    (globalSectionsPullback b ((higherDirectImage f q).obj F) ≫
      (globalSections T).map
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S Y T
          hDomainDerived hDomainBaseDerived hCodomainDerived hCodomainBaseDerived
          f fT b r h q).app F ≫
          (higherDirectImage fT q).map φ)).hom.comp (cohomologyToHigherSections f F q) =
      (cohomologyToHigherSections fT G q).comp
        ((Sheaf.H.map φ q).comp (cohomologyPullback.{u, w, w'} r F q)) := by
  rw [higherBaseChangeMapFromDerived_eq]
  let Γ : AbelianSheaf.{u, u + 1} T ⥤ AddCommGrpCat.{u + 1} := globalSections T
  let β : (inverseImage b).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage fT q).obj ((inverseImage r).obj F) :=
    (higherBaseChangeMap f fT b r h q).app F
  have hs : (Γ.map β).hom.comp
      ((globalSectionsPullback b ((higherDirectImage f q).obj F)).hom.comp
        (cohomologyToHigherSections f F q)) =
      (cohomologyToHigherSections fT ((inverseImage r).obj F) q).comp
        (cohomologyPullback.{u, w, w'} r F q) :=
    addHom_eq_of_apply _ _
      (@higherBaseChangeMap_cohomologyToHigherSections.{u, w, w'}
        X S Y T hDomainExt hCodomainExt f fT b r h F q)
  have ht : (Γ.map ((higherDirectImage fT q).map φ)).hom.comp
      (cohomologyToHigherSections fT ((inverseImage r).obj F) q) =
      (cohomologyToHigherSections fT G q).comp (Sheaf.H.map φ q) :=
    addHom_eq_of_apply _ _ (cohomologyToHigherSections_naturality fT φ q)
  exact mapped_coefficient_hom Γ β ((higherDirectImage fT q).map φ)
    ((globalSectionsPullback b ((higherDirectImage f q).obj F)).hom.comp
      (cohomologyToHigherSections f F q))
    (cohomologyToHigherSections fT ((inverseImage r).obj F) q)
    (cohomologyToHigherSections fT G q) (cohomologyPullback.{u, w, w'} r F q)
    (Sheaf.H.map φ q) hs ht

/-- Use the actual original coefficient-transfer value before native chart specialization. -/
private theorem higherBaseChangeMap_coefficientTransferSections_hom
    {X S Y T : Scheme.{u}}
    [hDomainExt : HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [hCodomainExt : HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [hDomainDerived : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [hDomainBaseDerived : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [hCodomainDerived : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} Y)]
    [hCodomainBaseDerived : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} T)]
    (f : X ⟶ S) (fT : Y ⟶ T) (b : T ⟶ S) (r : Y ⟶ X)
    (h : fT ≫ b = r ≫ f) (F : AbelianSheaf.{u, u + 1} X)
    (G : AbelianSheaf.{u, u + 1} Y) (φ : (inverseImage r).obj F ⟶ G) (q : ℕ) :
    (globalSectionsPullback b ((higherDirectImage f q).obj F) ≫
      (globalSections T).map
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S Y T
          hDomainDerived hDomainBaseDerived hCodomainDerived hCodomainBaseDerived
          f fT b r h q).app F ≫
          (higherDirectImage fT q).map φ)).hom.comp (cohomologyToHigherSections f F q) =
      (cohomologyToHigherSections fT G q).comp
        (Continuity.cohomologyTransfer.{u, e} r φ q).hom := by
  exact higherBaseChangeMap_coefficientSections_hom.{u, e, e, dX, dS, dX', dS'}
    (hDomainExt := hDomainExt) (hCodomainExt := hCodomainExt)
    (hDomainDerived := hDomainDerived) (hDomainBaseDerived := hDomainBaseDerived)
    (hCodomainDerived := hCodomainDerived) (hCodomainBaseDerived := hCodomainBaseDerived)
    f fT b r h F G φ q

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (U : S.Etale)

variable
  [hXExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [hX'Ext : HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [hSourceSlice : HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})]
  [hTargetSlice : HasExt.{s'} (Sheaf ((Scheme.smallEtaleTopology X').over
    ((siteBaseChange f').obj ((siteBaseChange g).obj U)))
    AddCommGrpCat.{u + 1})]
  [hZU : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hZV : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
  [hDX : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hDS : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hDX' : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [hDS' : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [hDZU : HasDerivedCategory.{dZU} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hDU : HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]
  [hDZV : HasDerivedCategory.{dZV}
    (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
  [hDV : HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} ((siteBaseChange g).obj U).left)]

/-- The original source base derived model at its identity-functor presentation. -/
local instance neighborhoodBaseChangeSourceBaseIdentityHasDerivedCategory :
    HasDerivedCategory.{dU}
      (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj U.left)) := hDU

/-- The original target base derived model at its identity-functor presentation. -/
local instance neighborhoodBaseChangeTargetBaseIdentityHasDerivedCategory :
    HasDerivedCategory.{dV}
      (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj ((siteBaseChange g).obj U).left)) := hDV

local instance neighborhoodBaseChange_sourceChartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hZU

local instance neighborhoodBaseChange_sourceChartSiteExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj U).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hZU

local instance neighborhoodBaseChange_targetChartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f').obj ((siteBaseChange g).obj U)).left) := hZV

local instance neighborhoodBaseChange_targetChartSiteExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj
      ((siteBaseChange f').obj ((siteBaseChange g).obj U)).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hZV

section SectionMaps

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV

section OriginalMap

omit hDZU hDU hDZV hDV

/-- The complete original unit-and-higher-exchange map at the original section carriers. -/
def fibreProductBaseChangeSectionMap (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    ((higherDirectImage f q).obj F).obj.obj (op U) ⟶
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)).obj.obj
        (op ((siteBaseChange g).obj U)) :=
  (@fibreProductBaseChangeSectionNatTrans.{u, dX, dS, dX', dS'} X S X' S'
    hDX hDS hDX' hDS' f f' g g' h U q).app F

/-- This is literally the original unit followed by the original higher exchange. -/
theorem fibreProductBaseChangeSectionMap_eq_original
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q =
      ((inverseImageAdjunction g).unit.app ((higherDirectImage f q).obj F)).hom.app (op U) ≫
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F).hom.app
          (op ((siteBaseChange g).obj U)) :=
  @fibreProductBaseChangeSectionNatTrans_app.{u, dX, dS, dX', dS'} X S X' S'
    hDX hDS hDX' hDS' f f' g g' h U q F

end OriginalMap

private theorem higherBaseChangeMap_sectionChart_square
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q ≫
        fibreProductChartSectionMap.{u, dX', dS', dZV, dV}
          f' ((siteBaseChange g).obj U)
          (hSourceDerived := hDX') (hTargetDerived := hDS')
          (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q =
      fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q ≫
        globalSectionsPullback (pullback.fst U.hom g)
          ((higherDirectImage (pullback.fst U.hom f) q).obj
            ((inverseImage (pullback.snd U.hom f)).obj F)) ≫
        (globalSections ((siteBaseChange g).obj U).left).map
          ((@higherBaseChangeMapFromDerived.{u, dZU, dU, dZV, dV}
            (pullback U.hom f) U.left
            (pullback ((siteBaseChange g).obj U).hom f') ((siteBaseChange g).obj U).left
            hDZU hDU hDZV hDV (pullback.fst U.hom f)
            (pullback.fst ((siteBaseChange g).obj U).hom f')
            (pullback.fst U.hom g) (fibreProductBaseChangeMap f f' g g' h U)
            (fibreProductBaseChangeMap_fst f f' g g' h U).symm q).app
              ((inverseImage (pullback.snd U.hom f)).obj F) ≫
            (higherDirectImage (pullback.fst ((siteBaseChange g).obj U).hom f') q).map
              ((inverseImageSquareIso (pullback.snd U.hom f)
                (pullback.snd ((siteBaseChange g).obj U).hom f') g'
                (fibreProductBaseChangeMap f f' g g' h U)
                (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F)) := by
  rw [fibreProductChartSectionMap_eq_family.{u, dX', dS', dZV, dV}
    f' ((siteBaseChange g).obj U)
    (hSourceDerived := hDX') (hTargetDerived := hDS')
    (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q,
    fibreProductChartSectionMap_eq_family.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q]
  exact higherBaseChangeMap_sectionChart_square_app.{u, dX, dS, dX', dS', dZU, dU, dZV, dV}
    f f' g g' h U (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
    (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) q F

end SectionMaps

set_option maxHeartbeats 500000 in
-- Allow finite extra elaboration for this eight-model native specialization.
-- Its comparisons and cancellation are equalities of whole additive maps.
private theorem higherBaseChangeMap_fibreProductSection_whole
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) =
      (fibreProductCohomologySectionHom.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q).comp
          (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f') g'
              (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom := by
  have : IsIso (fibreProductChartSectionMap.{u, dX', dS', dZV, dV}
      f' ((siteBaseChange g).obj U)
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q) :=
    fibreProductChartSectionMap_isIso.{u, dX', dS', dZV, dV}
      f' ((siteBaseChange g).obj U)
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q
  -- Keep the original chart and coefficient values literal at this application boundary.
  exact sectionHom_cancel
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q)
    (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q)
    (fibreProductChartSectionMap.{u, dX', dS', dZV, dV} f' ((siteBaseChange g).obj U)
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q)
    (globalSectionsPullback (pullback.fst U.hom g)
        ((higherDirectImage (pullback.fst U.hom f) q).obj
          ((inverseImage (pullback.snd U.hom f)).obj F)) ≫
      (globalSections ((siteBaseChange g).obj U).left).map
        ((@higherBaseChangeMapFromDerived.{u, dZU, dU, dZV, dV}
          (pullback U.hom f) U.left
          (pullback ((siteBaseChange g).obj U).hom f') ((siteBaseChange g).obj U).left
          hDZU hDU hDZV hDV (pullback.fst U.hom f)
          (pullback.fst ((siteBaseChange g).obj U).hom f') (pullback.fst U.hom g)
          (fibreProductBaseChangeMap f f' g g' h U)
          (fibreProductBaseChangeMap_fst f f' g g' h U).symm q).app
            ((inverseImage (pullback.snd U.hom f)).obj F) ≫
          (higherDirectImage (pullback.fst ((siteBaseChange g).obj U).hom f') q).map
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f') g'
              (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F)))
    (fibreProductCohomologySectionHom.{u, w, s, e} f U F q)
    (fibreProductCohomologySectionHom.{u, w', s', e} f' ((siteBaseChange g).obj U)
      ((inverseImage g').obj F) q)
    (Continuity.cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom
    (cohomologyToHigherSections (pullback.fst U.hom f)
      ((inverseImage (pullback.snd U.hom f)).obj F) q)
    (cohomologyToHigherSections (pullback.fst ((siteBaseChange g).obj U).hom f')
      ((inverseImage (pullback.snd ((siteBaseChange g).obj U).hom f')).obj
        ((inverseImage g').obj F)) q)
    (higherBaseChangeMap_sectionChart_square.{u, dX, dS, dX', dS', dZU, dU, dZV, dV}
      f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
      (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q)
    (fibreProductChartSection_hom.{u, w, s, e, dX, dS, dZU, dU} f U
      (hSourceDerived := hDX) (hTargetDerived := hDS)
      (hChartDerived := hDZU) (hBase := hDU) F q)
    (higherBaseChangeMap_coefficientTransferSections_hom.{u, e, dZU, dU, dZV, dV}
      (hDomainExt := hZU) (hCodomainExt := hZV)
      (hDomainDerived := hDZU) (hDomainBaseDerived := hDU)
      (hCodomainDerived := hDZV) (hCodomainBaseDerived := hDV)
      (pullback.fst U.hom f) (pullback.fst ((siteBaseChange g).obj U).hom f')
      (pullback.fst U.hom g) (fibreProductBaseChangeMap f f' g g' h U)
      (fibreProductBaseChangeMap_fst f f' g g' h U).symm
      ((inverseImage (pullback.snd U.hom f)).obj F)
      ((inverseImage (pullback.snd ((siteBaseChange g).obj U).hom f')).obj
        ((inverseImage g').obj F))
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q)
    (fibreProductChartSection_hom.{u, w', s', e, dX', dS', dZV, dV}
      f' ((siteBaseChange g).obj U)
      (hSourceDerived := hDX') (hTargetDerived := hDS')
      (hChartDerived := hDZV) (hBase := hDV) ((inverseImage g').obj F) q)

/-- The original unit-and-exchange section map commutes with the exact original
coefficient-square cohomology transfer as an equality of additive maps. -/
theorem higherBaseChangeMap_fibreProductSection
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q).hom.comp
        (fibreProductCohomologySectionHom.{u, w, s, e} f U F q) =
      (fibreProductCohomologySectionHom.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q).comp
          (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f') g'
              (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom :=
  higherBaseChangeMap_fibreProductSection_whole.{u, w, w', s, s', e,
    dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U
    (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
    (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q

private theorem higherBaseChangeMap_fibreProductGerm_hom
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ S')
    (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U) :
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F) ≫
      (pointSmallEtale ζ).sheafFiber.map
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
          hDX hDS hDX' hDS' f f' g g' h q).app F)).hom.comp
          (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p) =
      (fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q ζ
        (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)).comp
          (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f') g'
              (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom := by
  let V : S'.Etale := (siteBaseChange g).obj U
  let L := (higherDirectImage f q).obj F
  let G := (inverseImage g').obj F
  let L' := (higherDirectImage f' q).obj G
  let β : (inverseImage g).obj L ⟶ L' :=
    (@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F
  let p' := CoefficientStalkBaseChange.pulledBackPoint g ζ U p
  exact germHom_of_sectionHom
    ((pointSmallEtale (ζ ≫ g)).toPresheafFiber U p L.obj)
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F))
    (((inverseImageAdjunction g).unit.app L).hom.app (op U)) (β.hom.app (op V))
    ((pointSmallEtale ζ).toPresheafFiber V p' ((inverseImage g).obj L).obj)
    ((pointSmallEtale ζ).sheafFiber.map
      ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
        hDX hDS hDX' hDS' f f' g g' h q).app F))
    ((pointSmallEtale ζ).toPresheafFiber V p' L'.obj)
    (fibreProductBaseChangeSectionMap.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q)
    (fibreProductBaseChangeSectionMap_eq_original.{u, dX, dS, dX', dS'} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q)
    (StalkInverseImage.germ_stalkUnitNatIso g ζ L U p)
    ((pointSmallEtale ζ).toPresheafFiber_naturality β.hom V p')
    (fibreProductCohomologySectionHom.{u, w, s, e} f U F q)
    (fibreProductCohomologySectionHom.{u, w', s', e} f' V G q)
    (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom
    (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p)
    (fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
      ((inverseImage g').obj F) q ζ (CoefficientStalkBaseChange.pulledBackPoint g ζ U p))
    (fibreProductGerm_eq_sectionHom.{u, w, s, e} f U F q (ζ ≫ g) p)
    (fibreProductGerm_eq_sectionHom.{u, w', s', e} f' V G q ζ p')
    (higherBaseChangeMap_fibreProductSection.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
      (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q)


/-- The original arbitrary-neighborhood germ exchange, retaining its original
stalk unit, actual pulled-back point and exact coefficient-square transfer. -/
theorem higherBaseChangeMap_fibreProductCohomologyGerm
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ S')
    (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
    (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (pointSmallEtale ζ).sheafFiber.map
        ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
          (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p y)) =
      fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
        ((inverseImage g').obj F) q ζ
        (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
        (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
          ((inverseImageSquareIso (pullback.snd U.hom f)
            (pullback.snd ((siteBaseChange g).obj U).hom f')
            g' (fibreProductBaseChangeMap f f' g g' h U)
            (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y) := by
  exact germHom_apply
    ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F))
    ((pointSmallEtale ζ).sheafFiber.map
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F))
    (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p)
    (fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
      ((inverseImage g').obj F) q ζ (CoefficientStalkBaseChange.pulledBackPoint g ζ U p))
    (Continuity.cohomologyTransfer (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q).hom
    (higherBaseChangeMap_fibreProductGerm_hom.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS')
      (hDZU := hDZU) (hDU := hDU) (hDZV := hDZV) (hDV := hDV) F q ζ p) y

end AlgebraicGeometry.Scheme.EtaleCohomology
