/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeNeighborhoodGerms
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricComparisonEquation

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

universe u w w' s s' e dX dS dX' dS' dZU dU dZV dV

attribute [local instance] hasSheafifyLarge

open Continuity Finite.GeometricNeighborhood

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ζ : Spec (.of Ω) ⟶ S')
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ V : S'.Etale, HasExt.{s'} (Sheaf ((Scheme.smallEtaleTopology X').over
    ((siteBaseChange f').obj V)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [∀ V : S'.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom f'))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f'))]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [∀ U : S.Etale, HasDerivedCategory.{dZU}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [∀ U : S.Etale, HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]
  [∀ V : S'.Etale, HasDerivedCategory.{dZV}
    (AbelianSheaf.{u, u + 1} (pullback V.hom f'))]
  [∀ V : S'.Etale, HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V.left)]
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

/-- Comparisons with the original pointed-germ formulas commute with the
original stalk unit and higher exchange over the same geometric point. -/
theorem geometricCohomologyComparison_exchange
    (b : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q)
    (b' : ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F)) →+
        Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q)
    (hb : ∀ (U : S.Etale) (p : (pointSmallEtale (ζ ≫ g)).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      b (fibreProductCohomologyGerm.{u, w, s, e} f U F q (ζ ≫ g) p y) =
        relativeCohomologyTransfer.{u, e} F q
          (geometricFibrePointedMap Ω (ζ ≫ g) f { obj := U, val := p }) y)
    (hb' : ∀ (V : S'.Etale) (p : (pointSmallEtale ζ).fiber.obj V)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd V.hom f')).obj
        ((inverseImage g').obj F)) q),
      b' (fibreProductCohomologyGerm.{u, w', s', e} f' V ((inverseImage g').obj F) q ζ p y) =
        relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
          (geometricFibrePointedMap Ω ζ f' { obj := V, val := p }) y)
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    b' (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((higherBaseChangeMap.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
          ((higherDirectImage f q).obj F) z)) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q (b z) :=
  geometricCohomologyComparison_pointwise_of_hom_neighborhoodGerms.{u, w, w', s, s', e}
    f f' g g' h ζ F q
    ((higherBaseChangeMap.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
    (fun U p y => higherBaseChangeMap_fibreProductCohomologyGerm.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h U F q ζ p y)
    b b' hb hb' z

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R Ω] [Algebra R' Ω]
  (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (j' : Spec (.of R') ⟶ S') [Etale j'] [Mono j']
  (hη : Spec.algebraMap R Ω ≫ j = ζ ≫ g) (hζ : Spec.algebraMap R' Ω ≫ j' = ζ)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R' Ω) AddCommGrpCat.{e}]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R' (GeometricEtaleColimit R' Ω) ≫ j') f'))]

/-- The two actual strict-local/geometric comparisons commute with the original
stalk exchange. No map between the chosen marked models is supplied. -/
theorem chartGeometricCohomologyComparison_exchange
    (z : ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    chartGeometricCohomologyComparison.{u, w', s', e} Ω ζ f' R' j' hζ ((inverseImage g').obj F) q
        (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((higherBaseChangeMap.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
          ((StalkInverseImage.stalkUnitNatIso g ζ).hom.app
            ((higherDirectImage f q).obj F) z)) =
      geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q
        (chartGeometricCohomologyComparison.{u, w, s, e} Ω (ζ ≫ g) f R j hη F q z) :=
  geometricCohomologyComparison_exchange.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV} f f' g g' h ζ F q
    (chartGeometricCohomologyComparison.{u, w, s, e} Ω (ζ ≫ g) f R j hη F q)
    (chartGeometricCohomologyComparison.{u, w', s', e} Ω ζ f' R' j' hζ ((inverseImage g').obj F) q)
    (fun U p y => chartGeometricCohomologyComparison_pointedGerm.{u, w, s, e} Ω (ζ ≫ g) f R j hη F q
      { obj := U, val := p } y)
    (fun V p y => chartGeometricCohomologyComparison_pointedGerm.{u, w', s', e} Ω ζ f' R' j' hζ
      ((inverseImage g').obj F) q { obj := V, val := p } y) z

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
