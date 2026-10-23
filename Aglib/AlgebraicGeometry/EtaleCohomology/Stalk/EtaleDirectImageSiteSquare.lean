/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Native test-scheme square and chart-adjunction counits -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

private theorem inverse_projection {C : Type*} [Category* C] {A B Z : C}
    (e : A ≅ B) (p : A ⟶ Z) (q : B ⟶ Z) (h : e.hom ≫ q = p) : e.inv ≫ p = q := by
  rw [← h, Iso.inv_hom_id_assoc]

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

private theorem siteBaseChangeComp_inv_fst_fst {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (U : X.Etale) :
    ((siteBaseChangeComp f g).inv.app U).left ≫ pullback.fst U.hom (g ≫ f) =
      pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f :=
  inverse_projection
    ((Scheme.Etale.forget T ⋙ Over.forget T).mapIso ((siteBaseChangeComp f g).app U))
    _ _ (siteBaseChangeComp_hom_fst_fst f g U)

/-- The native comparison of iterated base changes for a commuting scheme square. -/
def siteBaseChangeSquareIso {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    siteBaseChange g ⋙ siteBaseChange f' ≅ siteBaseChange f ⋙ siteBaseChange g' :=
  (siteBaseChangeComp g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => siteBaseChange k) h) ≪≫
      siteBaseChangeComp f g'

/-- The actual square comparison preserves projection to the original test object. -/
theorem siteBaseChangeSquareIso_fst_fst {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (U : S.Etale) :
    ((siteBaseChangeSquareIso f f' g g' h).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) g' ≫ pullback.fst U.hom f =
      pullback.fst (pullback.snd U.hom g) f' ≫ pullback.fst U.hom g := by
  simp only [siteBaseChangeSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, etaleHom_comp_left, Category.assoc,
    siteBaseChangeComp_hom_fst_fst, eqToIso.hom, eqToHom_app]
  exact (congrArg
    (fun k : ((siteBaseChange (f' ≫ g)).obj U).left ⟶ U.left =>
      ((siteBaseChangeComp g f').inv.app U).left ≫ k)
    (siteBaseChange_eqToHom_fst h U)).trans (siteBaseChangeComp_inv_fst_fst g f' U)

/-- The pasted chart comparison respects the two original site counits. -/
theorem siteEtaleDirectImageRestriction_counit {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [Etale g] (U : S.Etale) :
    (siteEtalePostcompose (pullback.snd g f)).map
        ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
          pullback.condition).hom.app U) ≫
        (siteEtalePostcomposeAdj (pullback.snd g f)).counit.app ((siteBaseChange f).obj U) =
      (siteEtaleDirectImageRestrictionIso f g).hom.app ((siteBaseChange g).obj U) ≫
        (siteBaseChange f).map ((siteEtalePostcomposeAdj g).counit.app U) := by
  let q := (siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
    pullback.condition).hom.app U
  apply MorphismProperty.Over.Hom.ext
  change q.left ≫ pullback.fst (pullback.snd U.hom f) (pullback.snd g f) =
    (pullbackRightPullbackFstIso g f (pullback.snd U.hom g)).hom ≫
      pullback.lift
        (pullback.fst (pullback.snd U.hom g ≫ g) f ≫ pullback.fst U.hom g)
        (pullback.snd (pullback.snd U.hom g ≫ g) f) _
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst,
      pullbackRightPullbackFstIso_hom_fst_assoc]
    exact siteBaseChangeSquareIso_fst_fst f (pullback.fst g f) g
      (pullback.snd g f) pullback.condition U
  · have hw : q.left ≫ pullback.snd (pullback.snd U.hom f) (pullback.snd g f) =
        pullback.snd (pullback.snd U.hom g) (pullback.fst g f) :=
      MorphismProperty.Over.w q
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    refine (congrArg (fun k => k ≫ pullback.snd g f) hw).trans ?_
    simp only [Category.assoc, pullback.lift_snd, pullbackRightPullbackFstIso_hom_snd]

end AlgebraicGeometry.Scheme.EtaleCohomology
