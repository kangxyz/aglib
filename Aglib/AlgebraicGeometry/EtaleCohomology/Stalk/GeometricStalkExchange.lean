/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricComparisonExchange

/-! # Actual geometric-stalk exchange from the actual local transfers

The original stalk unit and the common-point diagram identify the defined
higher exchange. Bijectivity of the two original local-to-geometric
transfers therefore proves invertibility of this exact stalk map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe v vD vE

private theorem isIso_of_additive_comparison {A B C : AddCommGrpCat.{v}}
    {D : Type vD} {E : Type vE} [AddCommGroup D] [AddCommGroup E]
    (unit : A ⟶ B) [IsIso unit] (exchange : B ⟶ C)
    (source : A →+ D) (target : C →+ E) (transfer : D →+ E)
    (hsource : Function.Bijective source) (htarget : Function.Bijective target)
    (htransfer : Function.Bijective transfer)
    (h : ∀ x, target ((unit ≫ exchange) x) = transfer (source x)) :
    IsIso exchange := by
  have heq : target ∘ (unit ≫ exchange) = transfer ∘ source := funext h
  have hcomp : Function.Bijective (target ∘ (unit ≫ exchange)) := by
    rw [heq]
    exact htransfer.comp hsource
  have ht : Function.Bijective (unit ≫ exchange) :=
    (htarget.of_comp_iff' (unit ≫ exchange)).mp hcomp
  have hi : IsIso (unit ≫ exchange) :=
    (ConcreteCategory.isIso_iff_bijective (unit ≫ exchange)).mpr ht
  exact (isIso_comp_left_iff unit exchange).mp hi

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
  (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R Ω] [Algebra R' Ω]
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

local instance geometricStalkExchangeSourceFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd (ζ ≫ g) f)).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (ζ ≫ g) f)))

local instance geometricStalkExchangeTargetFiberExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd ζ f')).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ζ f')))

local instance geometricStalkExchangeSourceApexExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pointedNeighborhoodBaseChangedCone R Ω j (ζ ≫ g) hη f).pt.left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))

local instance geometricStalkExchangeTargetApexExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pointedNeighborhoodBaseChangedCone R' Ω j' ζ hζ f').pt.left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R' (GeometricEtaleColimit R' Ω) ≫ j') f')))

/-- Bijectivity of the actual local transfers proves invertibility of the
defined higher exchange on the original geometric stalk. -/
theorem higherBaseChangeMap_geometricStalk_isIso_of_localTransfers
    (H : IsPullback g' f' f g)
    (hκ : Function.Bijective
      (relativeCohomologyTransfer.{u, e} F q (chartGeometricPointMap Ω (ζ ≫ g) f R j hη)))
    (hκ' : Function.Bijective
      (relativeCohomologyTransfer.{u, e} ((inverseImage g').obj F) q
        (chartGeometricPointMap Ω ζ f' R' j' hζ))) :
    IsIso (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)) := by
  let L := (higherDirectImage f q).obj F
  let sourceStalk : AddCommGrpCat.{u + 1} :=
    ((pointSmallEtale (ζ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj L
  let pulledBackStalk : AddCommGrpCat.{u + 1} :=
    ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((inverseImage g).obj L)
  let targetStalk : AddCommGrpCat.{u + 1} :=
    ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f' q).obj ((inverseImage g').obj F))
  let v : sourceStalk ⟶ pulledBackStalk :=
    (StalkInverseImage.stalkUnitNatIso g ζ).hom.app L
  let β : pulledBackStalk ⟶ targetStalk :=
    ((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' h q).app F)
  let source : sourceStalk →+
      Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q :=
    chartGeometricCohomologyComparison.{u, w, s, e} Ω (ζ ≫ g) f R j hη F q
  let target : targetStalk →+
      Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q :=
    chartGeometricCohomologyComparison.{u, w', s', e}
      Ω ζ f' R' j' hζ ((inverseImage g').obj F) q
  let transfer :
      Sheaf.H.{e} ((inverseImage (pullback.snd (ζ ≫ g) f)).obj F) q →+
      Sheaf.H.{e} ((inverseImage (pullback.snd ζ f')).obj ((inverseImage g').obj F)) q :=
    (geometricFibreCohomologyTransfer.{u, e} f f' g g' h ζ F q).hom
  exact isIso_of_additive_comparison v β source target transfer
    (chartGeometricCohomologyComparison_bijective.{u, w, s, e}
      Ω (ζ ≫ g) f R j hη F q hκ)
    (chartGeometricCohomologyComparison_bijective.{u, w', s', e}
      Ω ζ f' R' j' hζ ((inverseImage g').obj F) q hκ')
    (geometricFibreCohomologyTransfer_bijective.{u, e} f f' g g' h ζ F q H)
    (fun z => chartGeometricCohomologyComparison_exchange.{u, w, w', s, s', e,
      dX, dS, dX', dS', dZU, dU, dZV, dV}
      (f := f) (f' := f') (g := g) (g' := g') (h := h) (ζ := ζ) (F := F) (q := q)
      (R := R) (R' := R') (j := j) (j' := j') (hη := hη) (hζ := hζ) z)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
