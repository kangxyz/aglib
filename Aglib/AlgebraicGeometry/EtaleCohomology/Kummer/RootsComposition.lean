/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.CategoryTheory.Adjunction.MateHomEquiv.Composition

/-!
# Composition of the original roots coefficient comparison

The literal root-section pullbacks compose through the original chart comparison. Taking
adjoints gives composition of the original positive-invertible roots inverse-image isomorphisms.
The proof concerns whole sheaf maps and introduces no geometric point or Galois-category premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

namespace GroupCohomology.Kummer.CoefficientBaseChange

universe u

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (n : ℕ)

-- Retain the original étale-chart projection reductions at this coefficient equation.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole original roots unit respects composition of arbitrary geometric pullbacks. -/
theorem rootsUnit_comp :
    rootsUnit f n ≫ (directImage f).map (rootsUnit g n) ≫
      (directImageCompIso f g).hom.app (mu Z n) = rootsUnit (g ≫ f) n := by
  ext W a
  apply (rootsSections Z n ((siteBaseChange (g ≫ f)).op.obj W)).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((rootsSections Z n ((siteBaseChange (g ≫ f)).op.obj W)
    ((mu Z n).obj.map ((siteBaseChangeComp f g).hom.app W.unop).op
      ((rootsUnit g n).hom.app ((siteBaseChange f).op.obj W)
        ((rootsUnit f n).hom.app W a)))).toMul).val = _
  let h := ((siteBaseChangeComp f g).hom.app W.unop).op
  let ag := (rootsUnit g n).hom.app ((siteBaseChange f).op.obj W)
    ((rootsUnit f n).hom.app W a)
  calc
    _ = Units.map h.unop.left.appTop.hom.toMonoidHom
        (rootsSections Z n ((siteBaseChange g).op.obj ((siteBaseChange f).op.obj W))
          ag).toMul.val := rootsSections_naturality Z n h ag
    _ = Units.map h.unop.left.appTop.hom.toMonoidHom
        (Units.map (pullback.fst ((siteBaseChange f).obj W.unop).hom g).appTop.hom.toMonoidHom
          (rootsSections Y n ((siteBaseChange f).op.obj W)
            ((rootsUnit f n).hom.app W a)).toMul.val) :=
      congrArg (Units.map h.unop.left.appTop.hom.toMonoidHom)
        (rootsUnit_sections g n ((siteBaseChange f).op.obj W) ((rootsUnit f n).hom.app W a))
    _ = Units.map h.unop.left.appTop.hom.toMonoidHom
        (Units.map (pullback.fst ((siteBaseChange f).obj W.unop).hom g).appTop.hom.toMonoidHom
          (Units.map (pullback.fst W.unop.hom f).appTop.hom.toMonoidHom
            (rootsSections X n W a).toMul.val)) :=
      congrArg (fun z => Units.map h.unop.left.appTop.hom.toMonoidHom
        (Units.map (pullback.fst ((siteBaseChange f).obj W.unop).hom g).appTop.hom.toMonoidHom z))
          (rootsUnit_sections f n W a)
    _ = Units.map (pullback.fst W.unop.hom (g ≫ f)).appTop.hom.toMonoidHom
        (rootsSections X n W a).toMul.val := by
      apply Units.ext
      exact congrArg (fun q : ((siteBaseChange (g ≫ f)).obj W.unop).left ⟶ W.unop.left =>
        q.appTop (rootsSections X n W a).toMul.val.val)
        (siteBaseChangeComp_hom_fst_fst f g W.unop)
    _ = _ := (rootsUnit_sections (g ≫ f) n W a).symm

/-- The original roots inverse-image map is the adjunct of its literal roots unit. -/
theorem rootsPullbackIso_homEquiv (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImageAdjunction f).homEquiv _ _ (rootsPullbackIso f n hn hinv).hom =
      rootsUnit f n :=
  rootsPullbackIso_unit f n hn hinv

/-- The original roots inverse-image isomorphisms compose on the whole coefficient sheaf. -/
theorem rootsPullbackIso_comp (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImageComp f g).hom.app (mu X n) ≫
        (inverseImage g).map (rootsPullbackIso f n hn hinv).hom ≫
        (rootsPullbackIso g n hn (levelInvertible f n hinv)).hom =
      (rootsPullbackIso (g ≫ f) n hn hinv).hom := by
  apply ((inverseImageAdjunction (g ≫ f)).homEquiv _ _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
    rootsPullbackIso_homEquiv]
  have h := Adjunction.homEquiv_leftAdjointCompIso_inv_map
    (inverseImageAdjunction f) (inverseImageAdjunction g)
    (inverseImageAdjunction (g ≫ f)) (directImageCompIso f g)
    (rootsPullbackIso f n hn hinv).hom
  change (inverseImageAdjunction (g ≫ f)).homEquiv _ _
      ((inverseImageComp f g).hom.app (mu X n) ≫
        (inverseImage g).map (rootsPullbackIso f n hn hinv).hom) = _ at h
  rw [h, rootsPullbackIso_homEquiv, Category.assoc, Category.assoc,
    ← (directImageCompIso f g).hom.naturality,
    Functor.comp_map, ← Functor.map_comp_assoc, rootsPullbackIso_unit,
    rootsUnit_comp]

/-- Equality of base maps retains the original roots inverse-image comparison. -/
theorem rootsPullbackIso_eqToHom {f g : Y ⟶ X} (h : f = g) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    eqToHom (congrArg (fun j => (inverseImage j).obj (mu X n)) h) ≫
      (rootsPullbackIso g n hn hinv).hom = (rootsPullbackIso f n hn hinv).hom := by
  subst g
  exact Category.id_comp _

end GroupCohomology.Kummer.CoefficientBaseChange
