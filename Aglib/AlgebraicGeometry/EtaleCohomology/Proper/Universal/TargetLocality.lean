/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.ModelTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.RelativeExchangeIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductBaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Etale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricAffineChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-! # Bounded proper exchange is local on its arbitrary target

An actual affine chart around the image of each geometric point reduces
the original exchange to the proper affine-target test. The two etale
chart exchanges and the original relative square give its inverse-image
restriction; the original point/stalk isomorphism then detects the map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

private theorem relative_pullback_of_pasting
    {C : Type*} [Category* C] {X S X' S' U V Z W : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (aU : U ⟶ S) (aV : V ⟶ S') (fU : Z ⟶ U) (fV : W ⟶ V)
    (piU : Z ⟶ X) (piV : W ⟶ X') (b : V ⟶ U) (r : W ⟶ Z)
    (H : IsPullback g' f' f g) (HU : IsPullback piU fU f aU)
    (HV : IsPullback piV fV f' aV)
    (hb : aV ≫ g = b ≫ aU) (hr : piV ≫ g' = r ≫ piU)
    (hR : fV ≫ b = r ≫ fU) : IsPullback r fV fU b := by
  have hOuter : IsPullback (r ≫ piU) fV f (b ≫ aU) := by
    rw [← hr, ← hb]
    exact HV.paste_horiz H
  exact hOuter.of_right hR.symm HU

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u dX dS dX' dS' dZU dU dZV dV

attribute [local instance] hasSheafifyLarge HasExt.standard HasDerivedCategory.standard

private theorem originalStalk_isIso_of_inverseImage
    {S T : Scheme.{u}} (a : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ T)
    {F G : AbelianSheaf.{u, u + 1} S} (β : F ⟶ G)
    [IsIso ((inverseImage a).map β)] :
    IsIso (((pointSmallEtale (ζ ≫ a)).sheafFiber (A := AddCommGrpCat.{u + 1})).map β) := by
  apply (NatIso.isIso_map_iff (StalkInverseImage.stalkUnitNatIso a ζ) β).mpr
  change IsIso (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
    ((inverseImage a).map β))
  infer_instance

private theorem killed_functor_obj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) [L.Additive]
    (n : ℕ) (F : C) (hF : n • 𝟙 F = 0) : n • 𝟙 (L.obj F) = 0 := by
  simpa using congrArg L.map hF

private theorem isIso_component_of_whole
    {C D : Type*} [Category* C] [Category* D]
    {L R : C ⥤ D} (α : L ⟶ R) [IsIso α] (M : C) : IsIso (α.app M) :=
  inferInstance

private theorem originalExchange_inverseImage_chart_isIso
    {X S X' S' : Scheme.{u}} (n : ℕ)
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g) (U : S.Etale)
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    [HasDerivedCategory.{dZU} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
    [hDU : HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]
    [HasDerivedCategory.{dZV}
      (AbelianSheaf.{u, u + 1} (pullback ((siteBaseChange g).obj U).hom f'))]
    [hDV : HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} ((siteBaseChange g).obj U).left)]
    (hChart : boundedBaseChange n (pullback.fst U.hom f))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((inverseImage ((siteBaseChange g).obj U).hom).map
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' H.w.symm q).app F)) := by
  let V : S'.Etale := (siteBaseChange g).obj U
  let : HasDerivedCategory.{dU}
      (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj U.left)) := hDU
  let : HasDerivedCategory.{dV}
      (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj V.left)) := hDV
  let fU : pullback U.hom f ⟶ U.left := pullback.fst U.hom f
  let fV : pullback V.hom f' ⟶ V.left := pullback.fst V.hom f'
  let piU : pullback U.hom f ⟶ X := pullback.snd U.hom f
  let piV : pullback V.hom f' ⟶ X' := pullback.snd V.hom f'
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  let r : pullback V.hom f' ⟶ pullback U.hom f :=
    fibreProductBaseChangeMap f f' g g' H.w.symm U
  have hU : fU ≫ U.hom = piU ≫ f := pullback.condition
  have hV : fV ≫ V.hom = piV ≫ f' := pullback.condition
  have hb : V.hom ≫ g = b ≫ U.hom :=
    (congrArg (fun k : V.left ⟶ S' => k ≫ g) (siteBaseChange_obj_hom g U)).trans
      pullback.condition.symm
  have hr : piV ≫ g' = r ≫ piU :=
    (fibreProductBaseChangeMap_snd f f' g g' H.w.symm U).symm
  have hR : fV ≫ b = r ≫ fU :=
    (fibreProductBaseChangeMap_fst f f' g g' H.w.symm U).symm
  have HU : IsPullback piU fU f U.hom := (IsPullback.of_hasPullback U.hom f).flip
  have HV : IsPullback piV fV f' V.hom := (IsPullback.of_hasPullback V.hom f').flip
  have HR : IsPullback r fV fU b :=
    relative_pullback_of_pasting f f' g g' U.hom V.hom fU fV piU piV b r H HU HV hb hr hR
  have hG : n • 𝟙 ((inverseImage piU).obj F) = 0 :=
    killed_functor_obj (inverseImage piU) n F hF
  have : IsIso ((higherBaseChangeMapFromDerived.{u, dZU, dU, dZV, dV}
    fU fV b r hR q).app ((inverseImage piU).obj F)) :=
    higherBaseChangeMap_isIso_of_boundedExchange.{u, dZU, dU, dZV, dV} fU fV b r hR n
      (hChart fV b r HR) ((inverseImage piU).obj F) hG q
  have : Etale U.hom := U.prop
  have : Etale V.hom := V.prop
  have hβU : IsIso
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} f fU U.hom piU hU q).app F) := by
    let : IsIso (higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} f fU U.hom piU hU q) :=
      by simpa only [higherBaseChangeMapFromDerived_eq] using
        (higherBaseChangeMap_etale_isIso.{u} f U.hom q)
    exact isIso_component_of_whole
      (higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} f fU U.hom piU hU q) F
  have hβV : IsIso
      ((higherBaseChangeMapFromDerived.{u, dX', dS', dZV, dV}
        f' fV V.hom piV hV q).app ((inverseImage g').obj F)) := by
    let : IsIso (higherBaseChangeMapFromDerived.{u, dX', dS', dZV, dV} f' fV V.hom piV hV q) :=
      by simpa only [higherBaseChangeMapFromDerived_eq] using
        (higherBaseChangeMap_etale_isIso.{u} f' V.hom q)
    exact isIso_component_of_whole
      (higherBaseChangeMapFromDerived.{u, dX', dS', dZV, dV} f' fV V.hom piV hV q)
      ((inverseImage g').obj F)
  exact higherBaseChangeMapFromDerived_inverseImage_isIso_of_chartRelative.{u, dX, dS, dX', dS',
      dZU, dU, dZV, dV}
    f f' g g' H.w.symm fU fV U.hom V.hom piU piV b r hU hV hb hr hR q F

private theorem originalExchange_geometricStalk_isIso_of_chart
    {X S X' S' : Scheme.{u}} (n : ℕ)
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g) (U : S.Etale)
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    (hChart : boundedBaseChange n (pullback.fst U.hom f))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ S')
    (p : Over.mk (ζ ≫ g) ⟶ (Scheme.Etale.forget S).obj U) :
    IsIso (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' H.w.symm q).app F)) := by
  let V : S'.Etale := (siteBaseChange g).obj U
  let β := (higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' H.w.symm q).app F
  have hβ : IsIso ((inverseImage V.hom).map β) :=
    originalExchange_inverseImage_chart_isIso.{u, dX, dS, dX', dS',
      u + 2, u + 2, u + 2, u + 2} n f f' g g' H U hChart F hF q
  let p' := CoefficientStalkBaseChange.pulledBackPoint g ζ U p
  have hp' : p'.left ≫ V.hom = ζ := Over.w p'
  have hpoint : IsIso
      (((pointSmallEtale (p'.left ≫ V.hom)).sheafFiber (A := AddCommGrpCat.{u + 1})).map β) :=
    originalStalk_isIso_of_inverseImage V.hom p'.left β
  change IsIso (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map β)
  exact Eq.mp (congrArg (fun η : Spec (.of Ω) ⟶ S' =>
    IsIso (((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map β)) hp') hpoint

private theorem boundedBaseChange_of_proper_affine_chart
    (n : ℕ)
    (hAffine : ∀ (R : Type u) [CommRing R] {Y : Scheme.{u}}
      (p : Y ⟶ Spec (.of R)) [IsProper p], boundedBaseChange n p)
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (R : Type u) [CommRing R] (j : Spec (.of R) ⟶ S) :
    boundedBaseChange n (pullback.fst j f) := by
  have : IsProper (pullback.fst j f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback j f).flip
      (inferInstance : IsProper f)
  intro Y' T' f' b b' HB
  exact hAffine R (pullback.fst j f) f' b b' HB

private theorem originalExchange_geometricStalk_isIso_of_etaleArrow
    {X S X' S' T : Scheme.{u}} (n : ℕ)
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g) (j : T ⟶ S) [Etale j]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    (hChart : boundedBaseChange n (pullback.fst j f))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ S')
    (t : Spec (.of Ω) ⟶ T) (ht : t ≫ j = ζ ≫ g) :
    IsIso (((pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' H.w.symm q).app F)) := by
  let U : S.Etale := Scheme.Etale.mk j
  have hj : U.hom = j := rfl
  have hChartU : boundedBaseChange n (pullback.fst U.hom f) :=
    @Eq.mp (boundedBaseChange n (pullback.fst j f))
      (boundedBaseChange n (pullback.fst U.hom f))
      (congrArg (fun a : T ⟶ S => boundedBaseChange n (pullback.fst a f)) hj.symm)
      @hChart
  let p : Over.mk (ζ ≫ g) ⟶ (Scheme.Etale.forget S).obj U := Over.homMk t ht
  exact originalExchange_geometricStalk_isIso_of_chart.{u, dX, dS, dX', dS'}
    n f f' g g' H U hChartU F hF q ζ p

private theorem originalExchange_isIso_of_proper_affineTargets
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    (n : ℕ)
    (hAffine : ∀ (R : Type u) [CommRing R] {Y : Scheme.{u}}
      (p : Y ⟶ Spec (.of R)) [IsProper p], boundedBaseChange n p)
    (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' H.w.symm q).app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 S')
  intro Ω _ _ ζ _
  obtain ⟨i, φ, hη⟩ := Finite.exists_affineOpenCover_point_factorization (ζ ≫ g)
  let R := S.affineOpenCover.X i
  let j : Spec (.of R) ⟶ S := S.affineOpenCover.f i
  have hChart : boundedBaseChange n (pullback.fst j f) :=
    @boundedBaseChange_of_proper_affine_chart n hAffine X S f inferInstance R inferInstance j
  exact originalExchange_geometricStalk_isIso_of_etaleArrow.{u, dX, dS, dX', dS'}
    n f f' g g' H j hChart F hF q ζ (Spec.map (CommRingCat.ofHom φ)) hη


private theorem originalExchange_isIso_of_proper_affineTargets_actual
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    (n : ℕ)
    (hAffine : ∀ (R : Type u) [CommRing R] {Y : Scheme.{u}}
      (p : Y ⟶ Spec (.of R)) [IsProper p], boundedBaseChange n p)
    (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ)
    {β : (inverseImage g).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage f' q).obj ((inverseImage g').obj F)}
    (hβ : β = (higherBaseChangeMapFromDerived.{u, dX, dS, dX', dS'} f f' g g' H.w.symm q).app F) :
    IsIso β := by
  subst β
  exact originalExchange_isIso_of_proper_affineTargets.{u, dX, dS, dX', dS'}
    n hAffine f f' g g' H F hF q

private theorem boundedExchange_of_proper_affineTargets
    (n : ℕ)
    (hAffine : ∀ (R : Type u) [CommRing R] {Y : Scheme.{u}}
      (p : Y ⟶ Spec (.of R)) [IsProper p], boundedBaseChange n p)
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (H : IsPullback g' f' f g) :
    boundedExchange n f f' g g' H.w.symm := by
  intro F hF q
  let hDX := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let hDS := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let hDX' := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let hDS' := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  refine @originalExchange_isIso_of_proper_affineTargets_actual.{u, u + 2, u + 2, u + 2, u + 2}
    X S X' S' hDX hDS hDX' hDS'
    n hAffine f inferInstance f' g g' H F hF q _ ?_
  exact (NatTrans.congr_app
    (@higherBaseChangeMapFromDerived_eq.{u, u + 2, u + 2, u + 2, u + 2}
      X S X' S' hDX hDS hDX' hDS' f f' g g' H.w.symm q) F).symm

/-- Actual bounded proper exchange over every spectrum supplies the original
bounded proper exchange over every scheme. No global finiteness assumption
on the target is introduced. -/
theorem boundedBaseChange_proper_of_affineTargets
    (n : ℕ)
    (hAffine : ∀ (R : Type u) [CommRing R] {Y : Scheme.{u}}
      (p : Y ⟶ Spec (.of R)) [IsProper p], boundedBaseChange n p)
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] : boundedBaseChange n f := by
  intro X' S' f' g g' H
  exact boundedExchange_of_proper_affineTargets n hAffine f f' g g' H

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
