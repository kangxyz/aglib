/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricComparisonCore

/-! # Original geometric comparison equations from raw neighborhood laws

The original public API is retained over the unique construction in
`GeometricComparisonCore`. Actual exchange consumers may import that core
without importing these independently stated raw-law comparison theorems.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u w w' s s' e dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

open Continuity Finite.GeometricNeighborhood

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [hΩField : Field Ω] [hΩSep : IsSepClosed Ω]
  (ζ : Spec (.of Ω) ⟶ S')
  [hXExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [hX'Ext : HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [hSourceSlice : ∀ U : S.Etale, HasExt.{s}
    (Sheaf (@GrothendieckTopology.over.{u, u + 1} X.Etale
      (inferInstance : Category.{u} X.Etale) (Scheme.smallEtaleTopology X)
      ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hTargetSlice : ∀ V : S'.Etale, HasExt.{s'}
    (Sheaf (@GrothendieckTopology.over.{u, u + 1} X'.Etale
      (inferInstance : Category.{u} X'.Etale) (Scheme.smallEtaleTopology X')
      ((siteBaseChange f').obj V)) AddCommGrpCat.{u + 1})]
  [hZU : ∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hZV : ∀ V : S'.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom f'))]
  [hFiber : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))]
  [hFiber' : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))]

attribute [local instance] geometricEquationSourceFiberExt
  geometricEquationTargetFiberExt geometricEquationSourceNeighborhoodExt
  geometricEquationTargetNeighborhoodExt

section ActualMap

variable (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

set_option maxHeartbeats 500000 in
-- The original germ-extensionality application elaborates several independent coefficient worlds.
/-- Original germ laws and the actual coefficient rectangle give the pointwise
comparison through the original germ extensionality theorem. -/
theorem geometricCohomologyComparison_pointwise_of_hom_neighborhoodGerms
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (hN : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      (pointSmallEtale ζ).sheafFiber.map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) =
        @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (Continuity.cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      b (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
        hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    : ∀ z, b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) := by
  have hsquare := IndexedGermComparisonData.ofMaps_square
    (fun U p y => @fibreProductCohomologyGerm.{u, w, s, e} X S f U
      hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)
    (fun V p y => @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
      hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y)
    (siteBaseChange g).obj (CoefficientStalkBaseChange.pulledBackPoint g ζ)
    (fun z => ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β
      ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F) z))
    (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q)
    (fun U => cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q)
    (fun U p => relativeCohomologyTransfer.{u, e} F q
      (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
    (fun V p => relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
      (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }))
    (exists_fibreProductCohomologyGerm.{u, w, s, e} f F q (ζ ≫ g))
    (fun U p => geometricCohomologyComparison_neighborhood_whole.{u, e} f f' g g' h ζ
      (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber') F q U p)
    hN b b' hb hb'
  exact hsquare

/-- Original neighborhood representatives and the literal geometric rectangle
compare any actual sheaf morphism satisfying the stated original germ formula.
No derived-category data is present in this native specialization. -/
theorem geometricCohomologyComparison_of_hom_neighborhoodGerms
    (β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F))
    (hN : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      (pointSmallEtale ζ).sheafFiber.map β
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) =
        @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (Continuity.cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      b (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
        hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    : geometricCohomologyComparisonEquationOfHom.{u, e} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber') F q β b b' :=
  (geometricCohomologyComparisonEquationOfHom_iff_original.{u, e}
    f f' g g' h ζ (hFiber := hFiber) (hFiber' := hFiber') F q β b b').2
    (geometricCohomologyComparison_pointwise_of_hom_neighborhoodGerms.{u, w, w', s, s', e}
      f f' g g' h ζ
      (hXExt := hXExt) (hX'Ext := hX'Ext)
      (hSourceSlice := hSourceSlice) (hTargetSlice := hTargetSlice)
      (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber') F q
      β hN b b' hb hb')

end ActualMap

variable
  [hDX : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hDS : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hDX' : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [hDS' : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The original stalk unit followed by the stalk of the original higher
exchange, shared before its application to a representative. -/
def higherBaseChangeStalkMap :
    ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
    ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) :=
  higherDirectImageStalkMapOfHom.{u} f f' g g' ζ F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F)

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV hFiber hFiber' in
/-- The shared map is literally the original stalk-unit/exchange composite. -/
theorem higherBaseChangeStalkMap_apply
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    higherBaseChangeStalkMap.{u, dX, dS, dX', dS'} f f' g g' h ζ
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q z =
      ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
        hDX hDS hDX' hDS' f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
          ((higherDirectImage f q).obj F) z) := rfl

/-- The literal common-point square for the original stalk exchange and
geometric coefficient transfer, retained through its producer and consumer. -/
def geometricCohomologyComparisonEquation
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) : Prop :=
  geometricCohomologyComparisonEquationOfHom.{u, e} f f' g g' h ζ
    (hFiber := hFiber) (hFiber' := hFiber') F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F) b b'

omit hXExt hX'Ext hSourceSlice hTargetSlice hZU hZV in
/-- Expanding the shared equation recovers the original scalar formula. -/
theorem geometricCohomologyComparisonEquation_iff_original
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q) :
    geometricCohomologyComparisonEquation.{u, e, dX, dS, dX', dS'} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber')
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q b b' ↔
      ∀ z, b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
        hDX hDS hDX' hDS' f f' g g' h q).app F)
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
        geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) :=
  geometricCohomologyComparisonEquationOfHom_iff_original.{u, e} f f' g g' h ζ
    (hFiber := hFiber) (hFiber' := hFiber') F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F) b b'

/-- Comparisons with the original pointed-germ formulas commute with the
original stalk unit and higher exchange over the same geometric point. -/
theorem geometricCohomologyComparison_exchange_of_neighborhoodGerms
    (hN : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      (pointSmallEtale ζ).sheafFiber.map
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
          hDX hDS hDX' hDS' f f' g g' h q).app F)
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F)
            (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y)) =
        @fibreProductCohomologyGerm.{u, w', s', e} X' S' f' ((siteBaseChange g).obj U)
          hX'Ext (hTargetSlice ((siteBaseChange g).obj U)) (hZV ((siteBaseChange g).obj U))
          ((inverseImage g').obj F) q Ω hΩField hΩSep ζ
          (CoefficientStalkBaseChange.pulledBackPoint g ζ U p)
          (Continuity.cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
            ((inverseImageSquareIso (pullback.snd U.hom f)
              (pullback.snd ((siteBaseChange g).obj U).hom f')
              g' (fibreProductBaseChangeMap f f' g g' h U)
              (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q y))
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      b (@fibreProductCohomologyGerm.{u, w, s, e} X S f U
              hXExt (hSourceSlice U) (hZU U) F q Ω hΩField hΩSep (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (@fibreProductCohomologyGerm.{u, w', s', e} X' S' f' V
        hX'Ext (hTargetSlice V) (hZV V) ((inverseImage g').obj F) q Ω hΩField hΩSep ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    : geometricCohomologyComparisonEquation.{u, e, dX, dS, dX', dS'} f f' g g' h ζ
      (hFiber := hFiber) (hFiber' := hFiber')
      (hDX := hDX) (hDS := hDS) (hDX' := hDX') (hDS' := hDS') F q b b' :=
  geometricCohomologyComparison_of_hom_neighborhoodGerms.{u, w, w', s, s', e}
    f f' g g' h ζ
    (hXExt := hXExt) (hX'Ext := hX'Ext)
    (hSourceSlice := hSourceSlice) (hTargetSlice := hTargetSlice)
    (hZU := hZU) (hZV := hZV) (hFiber := hFiber) (hFiber' := hFiber') F q
    ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
      hDX hDS hDX' hDS' f f' g g' h q).app F) hN b b' hb hb'

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
