/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition

/-!
# Composition of the original inverse-image units on etale test objects

This is the low-level adjunction supplier for the inverse-image composition
unit equation. The older `H1/CoefficientStalkBaseChange.inverseImageComp_unit`
contains the reverse equation behind the torsor/naturality import chain. During
shared-source integration that proof should delegate to this supplier; the
read-only shared file is intentionally not edited here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology
attribute [local instance] hasSheafifyLarge

/-- The original adjunction units compose through the original inverse-image
comparison and the actual iterated-pullback comparison of test schemes. -/
@[reassoc]
lemma inverseImageUnit_comp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (F : AbelianSheaf.{u, u + 1} X) (U : X.Etale) :
    ((inverseImageAdjunction f).unit.app F).hom.app (op U) ≫
        ((inverseImageAdjunction g).unit.app ((inverseImage f).obj F)).hom.app
          (op ((siteBaseChange f).obj U)) ≫
        ((inverseImage g).obj ((inverseImage f).obj F)).obj.map
          ((siteBaseChangeComp f g).hom.app U).op =
      ((inverseImageAdjunction (g ≫ f)).unit.app F).hom.app (op U) ≫
        ((inverseImageComp f g).hom.app F).hom.app
          (op ((siteBaseChange (g ≫ f)).obj U)) := by
  let e := Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology T.smallEtaleTopology
  have h := unit_conjugateEquiv
    ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
    (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom F
  have he : conjugateEquiv
      ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
      (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom = e.hom :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (inverseImageAdjunction f) (inverseImageAdjunction g)
      (inverseImageAdjunction (g ≫ f)) e
  rw [he, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun q => q.hom.app (op U)) h
  have heU : (e.hom.app ((inverseImage g).obj ((inverseImage f).obj F))).hom.app (op U) =
      ((inverseImage g).obj ((inverseImage f).obj F)).obj.map
        ((siteBaseChangeComp f g).hom.app U).op := rfl
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h'
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k =>
      (((inverseImageAdjunction f).unit.app F).hom.app (op U) ≫
        ((inverseImageAdjunction g).unit.app ((inverseImage f).obj F)).hom.app
          (op ((siteBaseChange f).obj U))) ≫ k) heU.symm).trans h')

end AlgebraicGeometry.Scheme.EtaleAffineBasis
