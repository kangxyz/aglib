/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeNeighborhoodGerms
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricComparisonCore

/-! # The original higher exchange over a common geometric point

The original exchange commutes with comparisons to the two geometric fibres.
The proof uses its original neighborhood-germ formula and the actual
coefficient rectangle. The chosen strict-local models are independent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u vG w w' s s' e dX dS dX' dS' dZU dU dZV dV

attribute [local instance] hasSheafifyLarge

open Continuity Finite.GeometricNeighborhood

/-- Paste the original unit square and the two comparison triangles on one
fixed generator. No family of geometric comparison data is constructed here. -/
private theorem germComparisonSquare_apply
    {V W C D : AddCommGrpCat.{e}} {A B : Type*}
    [AddCommGroup A] [AddCommGroup B]
    (γ : V →+ A) (γ' : W →+ B) (m : A →+ B)
    (t : V ⟶ W) (r : V ⟶ C) (r' : W ⟶ D) (d : C ⟶ D)
    (b : A →+ C) (b' : B →+ D)
    (hunit : m.comp γ = γ'.comp t.hom)
    (hsource : ∀ y, b (γ y) = r y)
    (htarget : ∀ y, b' (γ' y) = r' y)
    (hrectangle : t ≫ r' = r ≫ d) (y : V) :
    b' (m (γ y)) = d (b (γ y)) := by
  calc
    b' (m (γ y)) = b' (γ' (t y)) :=
      congrArg b' (DFunLike.congr_fun hunit y)
    _ = r' (t y) := htarget (t y)
    _ = d (r y) := ConcreteCategory.congr_hom hrectangle y
    _ = d (b (γ y)) := congrArg d (hsource y).symm

section NeighborhoodComparison

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X S : Scheme.{u}}
  (η : Spec (.of Ω) ⟶ S) (f : X ⟶ S)
  (R : Type u) [CommRing R] [Algebra R Ω]
  (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (hη : Spec.algebraMap R Ω ≫ j = η)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback η f))]
  [QuasiCompact f] [QuasiSeparated f]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance neighborhoodComparisonFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd η f)).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback η f)))

local instance neighborhoodComparisonStageExt
    (d : (pointSmallEtale η).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω η f).obj d).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback d.obj.hom f)))

/-- Normalize the complete original germ property at one point before it is
supplied to the comparison with independent source and target derived models. -/
private theorem chartGeometricComparison_neighborhoodGerms :
    ∀ (U : S.Etale) (p : (pointSmallEtale η).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      chartGeometricCohomologyComparison.{u, w, s, e} Ω η f R j hη F q
          (fibreProductCohomologyGerm.{u, w, s, e} f U F q η p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω η f { obj := U, val := p }) y := by
  intro U p y
  have h := chartGeometricCohomologyComparison_pointedGerm.{u, w, s, e}
    Ω η f R j hη F q { obj := U, val := p }
  dsimp only at h
  exact h y

end NeighborhoodComparison

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [hOmegaField : Field Ω] [hOmegaClosed : IsSepClosed Ω]
  (ζ : Spec (.of Ω) ⟶ S')
  [hSourceExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [hTargetExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [hSourceSlices : ∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hTargetSlices : ∀ V : S'.Etale, HasExt.{s'} (Sheaf ((Scheme.smallEtaleTopology X').over
    ((siteBaseChange f').obj V)) AddCommGrpCat.{u + 1})]
  [hSourceStages : ∀ U : S.Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hTargetStages : ∀ V : S'.Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom f'))]
  [hSourceGeometricExt : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))]
  [hTargetGeometricExt : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))]
  [hSourceDerived : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hSourceBaseDerived : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hTargetDerived : HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [hTargetBaseDerived : HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [hSourceChartDerived : ∀ U : S.Etale, HasDerivedCategory.{dZU}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hSourceChartBaseDerived : ∀ U : S.Etale,
    HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]
  [hTargetChartDerived : ∀ V : S'.Etale, HasDerivedCategory.{dZV}
    (AbelianSheaf.{u, u + 1} (pullback V.hom f'))]
  [hTargetChartBaseDerived : ∀ V : S'.Etale,
    HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V.left)]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance geometricExchangeSourceFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd (ζ ≫ g) f)).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f)))

local instance geometricExchangeTargetFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd ζ f')).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f')))

local instance geometricExchangeSourceNeighborhoodExt
    (d : (pointSmallEtale (ζ ≫ g)).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω (ζ ≫ g) f).obj d).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback d.obj.hom f)))

local instance geometricExchangeTargetNeighborhoodExt
    (d : (pointSmallEtale ζ).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω ζ f').obj d).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback d.obj.hom f')))

/-- On a fixed original germ, paste the original higher-exchange square,
comparison triangles and geometric coefficient rectangle. -/
private theorem geometricExchange_on_germ
    (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (V : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f)).obj F) q),
      b (fibreProductCohomologyGerm.{u, w, s, e} f V F q (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := V, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (fibreProductCohomologyGerm.{u, w', s', e} f' V
        ((inverseImage g').obj F) q ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
          ((higherDirectImage f q).obj F)
          (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p y))) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
        (b (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p y)) := by
  exact germComparisonSquare_apply
    (V := AddCommGrpCat.of
      (Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q))
    (W := AddCommGrpCat.of
      (Sheaf.H.{e} ((inverseImage (pullback.snd ((siteBaseChange g).obj U).hom f')).obj
        ((inverseImage g').obj F)) q))
    (C := AddCommGrpCat.of
      (Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q))
    (D := AddCommGrpCat.of
      (Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q))
    (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p)
    (fibreProductCohomologyGerm.{u, w', s', e} f' ((siteBaseChange g).obj U)
      ((inverseImage g').obj F) q ζ (CoefficientStalkBaseChange.pulledBackPoint g ζ U p))
    (((StalkInverseImage.stalkUnitNatIso g ζ).hom.app ((higherDirectImage f q).obj F) ≫
      ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)).hom)
    (cohomologyTransfer.{u, e} (fibreProductBaseChangeMap f f' g g' h U)
      (F := (inverseImage (pullback.snd U.hom f)).obj F)
      (G := (inverseImage (pullback.snd ((siteBaseChange g).obj U).hom f')).obj
        ((inverseImage g').obj F))
      ((inverseImageSquareIso (pullback.snd U.hom f)
        (pullback.snd ((siteBaseChange g).obj U).hom f') g'
        (fibreProductBaseChangeMap f f' g g' h U)
        (fibreProductBaseChangeMap_snd f f' g g' h U).symm).inv.app F) q)
    (relativeCohomologyTransfer.{u, e} F q
      (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }))
    (relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
      (geometricFibrePointedMap Ω ζ f'
        { obj := (siteBaseChange g).obj U
          val := CoefficientStalkBaseChange.pulledBackPoint g ζ U p }))
    (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q) b b'
    (higherBaseChangeMap_fibreProductGerm_hom.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U F q ζ p)
    (hb U p)
    (hb' ((siteBaseChange g).obj U) (CoefficientStalkBaseChange.pulledBackPoint g ζ U p))
    (geometricCohomologyComparison_neighborhood_whole.{u, e}
      f f' g g' h ζ F q U p) y

/-- Comparisons with the original pointed-germ formulas commute with the
original stalk unit and higher exchange over the same geometric point. -/
theorem geometricCohomologyComparison_exchange
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : (geometricCohomologyComparisonData f f' g g' h ζ
      (hXExt := hSourceExt) (hX'Ext := hTargetExt)
      (hSourceSlice := hSourceSlices) (hTargetSlice := hTargetSlices)
      (hZU := hSourceStages) (hZV := hTargetStages)
      (hFiber := hSourceGeometricExt) (hFiber' := hTargetGeometricExt) F q
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)).SourceLaw b)
    (hb' : (geometricCohomologyComparisonData f f' g g' h ζ
      (hXExt := hSourceExt) (hX'Ext := hTargetExt)
      (hSourceSlice := hSourceSlices) (hTargetSlice := hTargetSlices)
      (hZU := hSourceStages) (hZV := hTargetStages)
      (hFiber := hSourceGeometricExt) (hFiber' := hTargetGeometricExt) F q
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)).TargetLaw b')
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
          ((higherDirectImage f q).obj F) z)) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) := by
  obtain ⟨U, p, y, rfl⟩ := exists_fibreProductCohomologyGerm.{u, w, s, e}
    f F q (ζ ≫ g) z
  exact geometricExchange_on_germ.{u, w, w', s, s', e,
    dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h ζ F q U p b b'
    ((geometricCohomologyComparisonData_sourceLaw_iff.{u, w, w', s, s', e}
      f f' g g' h ζ
      (hXExt := hSourceExt) (hX'Ext := hTargetExt)
      (hSourceSlice := hSourceSlices) (hTargetSlice := hTargetSlices)
      (hZU := hSourceStages) (hZV := hTargetStages)
      (hFiber := hSourceGeometricExt) (hFiber' := hTargetGeometricExt) F q
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F) b).mp hb)
    ((geometricCohomologyComparisonData_targetLaw_iff.{u, w, w', s, s', e}
      f f' g g' h ζ
      (hXExt := hSourceExt) (hX'Ext := hTargetExt)
      (hSourceSlice := hSourceSlices) (hTargetSlice := hTargetSlices)
      (hZU := hSourceStages) (hZV := hTargetStages)
      (hFiber := hSourceGeometricExt) (hFiber' := hTargetGeometricExt) F q
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F) b').mp hb') y

variable (R R' : Type u) [hSourceRing : CommRing R] [hTargetRing : CommRing R']
  [hSourceAlgebra : Algebra R Ω] [hTargetAlgebra : Algebra R' Ω]
  (j : Spec (.of R) ⟶ S) [hSourceEtale : Etale j] [hSourceMono : Mono j]
  (j' : Spec (.of R') ⟶ S') [hTargetEtale : Etale j'] [hTargetMono : Mono j']
  (hη : Spec.algebraMap R Ω ≫ j = ζ ≫ g) (hζ : Spec.algebraMap R' Ω ≫ j' = ζ)
  [hSourceQc : QuasiCompact f] [hSourceQs : QuasiSeparated f]
  [hTargetQc : QuasiCompact f'] [hTargetQs : QuasiSeparated f']
  [hSourceColimits : HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}]
  [hTargetColimits : HasColimitsOfShape (GeometricEtaleNeighborhood R' Ω) AddCommGrpCat.{e}]
  [hSourceLimitExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [hTargetLimitExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R' (GeometricEtaleColimit R' Ω) ≫ j') f'))]

/-- The two actual strict-local/geometric comparisons commute with the original
stalk exchange. No map between the chosen marked models is supplied. -/
theorem chartGeometricCohomologyComparison_exchange
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    (@chartGeometricCohomologyComparison.{u, w', s', e}
      Ω hOmegaField hOmegaClosed X' S' ζ f' R' hTargetRing hTargetAlgebra
      j' hTargetEtale hTargetMono hζ hTargetExt hTargetSlices hTargetStages
      hTargetLimitExt hTargetGeometricExt hTargetQc hTargetQs hTargetColimits
      ((inverseImage g').obj F) q)
        (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((@higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} X S X' S'
            hSourceDerived hSourceBaseDerived hTargetDerived hTargetBaseDerived
            f f' g g' h q).app F)
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
        ((@chartGeometricCohomologyComparison.{u, w, s, e}
      Ω hOmegaField hOmegaClosed X S (ζ ≫ g) f R hSourceRing hSourceAlgebra
      j hSourceEtale hSourceMono hη hSourceExt hSourceSlices hSourceStages
      hSourceLimitExt hSourceGeometricExt hSourceQc hSourceQs hSourceColimits F q) z) := by
  exact geometricCohomologyComparison_exchange.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h ζ F q
    (hOmegaField := hOmegaField) (hOmegaClosed := hOmegaClosed)
    (hSourceExt := hSourceExt) (hTargetExt := hTargetExt)
    (hSourceSlices := hSourceSlices) (hTargetSlices := hTargetSlices)
    (hSourceStages := hSourceStages) (hTargetStages := hTargetStages)
    (hSourceGeometricExt := hSourceGeometricExt) (hTargetGeometricExt := hTargetGeometricExt)
    (hSourceDerived := hSourceDerived) (hSourceBaseDerived := hSourceBaseDerived)
    (hTargetDerived := hTargetDerived) (hTargetBaseDerived := hTargetBaseDerived)
    (hSourceChartDerived := hSourceChartDerived)
    (hSourceChartBaseDerived := hSourceChartBaseDerived)
    (hTargetChartDerived := hTargetChartDerived)
    (hTargetChartBaseDerived := hTargetChartBaseDerived)
    (@chartGeometricCohomologyComparison.{u, w, s, e}
      Ω hOmegaField hOmegaClosed X S (ζ ≫ g) f R hSourceRing hSourceAlgebra
      j hSourceEtale hSourceMono hη hSourceExt hSourceSlices hSourceStages
      hSourceLimitExt hSourceGeometricExt hSourceQc hSourceQs hSourceColimits F q)
    (@chartGeometricCohomologyComparison.{u, w', s', e}
      Ω hOmegaField hOmegaClosed X' S' ζ f' R' hTargetRing hTargetAlgebra
      j' hTargetEtale hTargetMono hζ hTargetExt hTargetSlices hTargetStages
      hTargetLimitExt hTargetGeometricExt hTargetQc hTargetQs hTargetColimits
      ((inverseImage g').obj F) q)
    (chartGeometricComparison_neighborhoodGerms.{u, w, s, e}
      Ω (ζ ≫ g) f R j hη F q)
    (chartGeometricComparison_neighborhoodGerms.{u, w', s', e}
      Ω ζ f' R' j' hζ ((inverseImage g').obj F) q) z

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
