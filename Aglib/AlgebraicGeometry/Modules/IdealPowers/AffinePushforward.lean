/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.UnitQuotient
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.QuotientComparison
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward

/-!
# Actual ideal quotients commute with affine pushforward

The comparison factors through the actual infinitesimal thickenings and the
proved affine module base-change map. Its original quotient equation is retained;
no flatness assumption or non-affine pushforward comparison is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  (i : X ⟶ Y) [IsAffineHom i] (f : Y ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent] (J : Ideal A)

omit [IsAffineHom i] in
/-- Iterated and single actual ideal thickenings have the same kernel on X. -/
theorem idealThickeningComposite_ker :
    (idealThickeningι (i ≫ f) J).ker =
      (Limits.pullback.fst i (idealThickeningι f J)).ker := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let e := pullbackRightPullbackFstIso f q i
  calc
    (idealThickeningι (i ≫ f) J).ker =
        (e.hom ≫ idealThickeningι (i ≫ f) J).ker :=
      (Scheme.Hom.ker_comp_of_isIso e.hom _).symm
    _ = (Limits.pullback.fst i (idealThickeningι f J)).ker :=
      congrArg Scheme.Hom.ker (pullbackRightPullbackFstIso_hom_fst f q i)

/-- Pushforward by an affine morphism preserves the original coefficient quotient. -/
def affinePushforwardIdealQuotientIso :
    (pushforward i).obj (idealQuotient X
      ((i ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F J) ≅
    idealQuotient Y (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      ((pushforward i).obj F) J := by
  let : ((pushforward i).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom i F
  exact (pushforward i).mapIso (idealQuotientThickeningIso (i ≫ f) F J) ≪≫
    (pushforward i).mapIso (closedImmersionQuotientIso
      (idealThickeningι (i ≫ f) J) (Limits.pullback.fst i (idealThickeningι f J))
      (idealThickeningComposite_ker i f J) F) ≪≫
    affinePushforwardUnitIso i (idealThickeningι f J) F ≪≫
    (idealQuotientThickeningIso f ((pushforward i).obj F) J).symm

/-- The pushforward quotient isomorphism retains the original quotient morphisms. -/
@[reassoc]
theorem affinePushforwardIdealQuotientIso_π :
    (pushforward i).map (idealQuotientπ X
        ((f.appTop ≫ i.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F J) ≫
      (affinePushforwardIdealQuotientIso i f F J).hom =
    idealQuotientπ Y (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      ((pushforward i).obj F) J := by
  have hπ :
      (pushforward i).map (idealQuotientπ X
          ((i ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F J) ≫
        (affinePushforwardIdealQuotientIso i f F J).hom =
      idealQuotientπ Y (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
        ((pushforward i).obj F) J := by
    let : ((pushforward i).obj F).IsQuasicoherent :=
      isQuasicoherent_pushforward_of_isAffineHom i F
    dsimp only [affinePushforwardIdealQuotientIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom]
    rw [← Functor.map_comp_assoc, idealQuotientπ_thickeningIso_hom,
      ← Functor.map_comp_assoc, closedImmersionUnit_quotientIso_hom,
      affinePushforwardUnitIso_unit_assoc]
    change idealThickeningUnit f ((pushforward i).obj F) J ≫
        (idealQuotientThickeningIso f ((pushforward i).obj F) J).inv = _
    rw [← idealQuotientπ_thickeningIso_hom, Category.assoc, Iso.hom_inv_id]
    exact Category.comp_id _
  simpa only [Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top] using hπ

end AlgebraicGeometry.Scheme.Modules
