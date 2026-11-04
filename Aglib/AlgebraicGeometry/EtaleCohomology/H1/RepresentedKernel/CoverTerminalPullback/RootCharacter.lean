/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverTerminalPullback
public import Aglib.AlgebraicGeometry.Group.BaseChange.PointTransport

/-! Root character base change on the original terminal marked row. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open Scheme.Group Scheme.Group.BaseChange Scheme.Group.MultiplicativeGroup
open Scheme.OverField Scheme.EtaleCohomology.RepresentedKernel
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Group.BaseChange

variable {S Y Z : Scheme.{u}}

private theorem rootsBaseChangeHom_comp (f : Z ⟶ Y) (g : Y ⟶ S) (n : ℕ) :
    (groupSchemeBaseChange f).functor.map (MultiplicativeBaseChange.rootsBaseChangeIso g n).hom ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom =
      (groupSchemeBaseChangeComp f g).inv.app (rootsGroupScheme S n) ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso (f ≫ g) n).hom := by
  apply (Grp.forget (Over Z)).map_injective
  let R := rootsGroupScheme S n
  have h : ((groupSchemeBaseChangeComp f g).inv.app R).hom.hom =
      MultiplicativeBaseChange.pullbackComposeMap f g R.X :=
    (groupSchemeBaseChangeComp_inv_app_hom_hom f g R).trans
      ((PointTransport.groupPullbackCompIso_hom f g R).symm.trans
        (PointTransport.groupPullbackCompIso_projection f g R))
  change (Over.pullback f).map (MultiplicativeBaseChange.rootsBaseChangeIso g n).hom.hom.hom ≫
      (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom.hom.hom =
    ((groupSchemeBaseChangeComp f g).inv.app R).hom.hom ≫
      (MultiplicativeBaseChange.rootsBaseChangeIso (f ≫ g) n).hom.hom.hom
  rw [h]
  exact MultiplicativeBaseChange.rootsBaseChangeIso_comp f g n

/-- Pull back the original terminal character to the original group over the direct base. -/
def terminalRootCharacterBaseChange (d : Z ⟶ S) (K : Grp (Over S)) (n : ℕ)
    (χ : baseChangedGroup (𝟙 S) K ⟶ rootsGroupScheme S n) :
    baseChangedGroup d K ⟶ rootsGroupScheme Z n :=
  (groupSchemeBaseChange d).functor.map (groupSchemeBaseChangeId.inv.app K ≫ χ) ≫
    (MultiplicativeBaseChange.rootsBaseChangeIso d n).hom

/-- The same two group comparisons as in the marked row preserve the original root character. -/
theorem terminalRootCharacterBaseChange_comp (f : Z ⟶ Y) (g : Y ⟶ S)
    (d : Z ⟶ S) (h : f ≫ g = d) (K : Grp (Over S)) (n : ℕ)
    (χ : baseChangedGroup (𝟙 S) K ⟶ rootsGroupScheme S n) :
    (groupSchemeBaseChangeComp f g).inv.app (baseChangedGroup (𝟙 S) K) ≫
        (terminalGroupComparison h).hom.app K ≫ terminalRootCharacterBaseChange d K n χ =
      (groupSchemeBaseChange f).functor.map
          ((groupSchemeBaseChange g).functor.map χ ≫
            (MultiplicativeBaseChange.rootsBaseChangeIso g n).hom) ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom := by
  subst d
  let b := f ≫ g
  let F := (groupSchemeBaseChange b).functor
  let j := groupSchemeBaseChangeId.app K
  let K₀ := baseChangedGroup (𝟙 S) K
  let U := (groupSchemeBaseChangeComp f g).inv.app K₀
  let V := (groupSchemeBaseChangeComp f g).inv.app (rootsGroupScheme S n)
  let r := (MultiplicativeBaseChange.rootsBaseChangeIso b n).hom
  have hJ : (terminalGroupComparison (rfl : b = b)).hom.app K = F.map j.hom := by
    simp only [terminalGroupComparison, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      groupSchemeBaseChangeCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
    change (F.map j.hom ≫ 𝟙 _) ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.comp_id]
  have hCancel : F.map j.hom ≫ F.map (j.inv ≫ χ) = F.map χ := by
    rw [← F.map_comp, Iso.hom_inv_id_assoc]
  have hNat := groupSchemeBaseChangeComp_inv_naturality f g χ
  change U ≫ (terminalGroupComparison (rfl : b = b)).hom.app K ≫
    (F.map (j.inv ≫ χ) ≫ r) = _
  rw [hJ, ← Category.assoc (F.map j.hom), hCancel]
  calc
    U ≫ F.map χ ≫ r =
        ((groupSchemeBaseChange f).functor.map
          ((groupSchemeBaseChange g).functor.map χ) ≫ V) ≫ r := by
      rw [← Category.assoc, hNat]
    _ = _ := by
      rw [Category.assoc, ← rootsBaseChangeHom_comp f g n, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Group.BaseChange
