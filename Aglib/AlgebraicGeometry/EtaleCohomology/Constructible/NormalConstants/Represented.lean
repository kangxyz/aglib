/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedBaseChange
public import Aglib.CategoryTheory.Sites.Continuous.KanUnit

/-! # Generic restriction of represented coefficients over a normal integral scheme

The original generic pullback is bijective on maps from every smooth scheme into
an integral morphism. Applied to the actual small-etale test objects, this proves
that the original inverse-image adjunction unit is an isomorphism for integral
etale represented coefficients. No Noetherian or quasi-compactness assumption is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.NormalConstants

universe u

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

private def genericMap (U Z : Over X)
    (h : (Over.pullback (X.fromSpecStalk (genericPoint X))).obj U ⟶
      (Over.pullback (X.fromSpecStalk (genericPoint X))).obj Z) :
    pullback (X.fromSpecStalk (genericPoint X)) U.hom ⟶ Z.left :=
  (pullbackSymmetry (X.fromSpecStalk (genericPoint X)) U.hom).hom ≫
    h.left ≫ pullback.fst Z.hom (X.fromSpecStalk (genericPoint X))

omit [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] in
private theorem genericMap_over (U Z : Over X)
    (h : (Over.pullback (X.fromSpecStalk (genericPoint X))).obj U ⟶
      (Over.pullback (X.fromSpecStalk (genericPoint X))).obj Z) :
    genericMap X U Z h ≫ Z.hom =
      pullback.snd (X.fromSpecStalk (genericPoint X)) U.hom ≫ U.hom := by
  have hw : h.left ≫ pullback.snd Z.hom (X.fromSpecStalk (genericPoint X)) =
      pullback.snd U.hom (X.fromSpecStalk (genericPoint X)) := Over.w h
  simp only [genericMap, Category.assoc, pullback.condition]
  rw [← Category.assoc h.left, hw]
  simp only [pullbackSymmetry_hom_comp_snd_assoc]
  exact pullback.condition

/-- The literal generic pullback is bijective on maps from any smooth test scheme
into an integral morphism over the given normal integral base. -/
theorem genericPullbackHom_bijective (U Z : Over X) [Smooth U.hom] [IsIntegralHom Z.hom] :
    Function.Bijective (fun h : U ⟶ Z =>
      (Over.pullback (X.fromSpecStalk (genericPoint X))).map h) := by
  constructor
  · intro f g h
    apply Over.OverMorphism.ext
    apply Scheme.genericFiber_hom_ext X U.hom Z.hom (Over.w f) (Over.w g)
    have hs := congrArg (fun t =>
      (pullbackSymmetry (X.fromSpecStalk (genericPoint X)) U.hom).hom ≫
        t.left ≫ pullback.fst Z.hom (X.fromSpecStalk (genericPoint X))) h
    simpa [Over.pullback, Category.assoc] using hs
  · intro h
    let f : U ⟶ Z := Over.homMk
      (Scheme.extendFromGenericFiber X U.hom Z.hom
        (genericMap X U Z h) (genericMap_over X U Z h))
      (Scheme.extendFromGenericFiber_over X U.hom Z.hom
        (genericMap X U Z h) (genericMap_over X U Z h))
    refine ⟨f, ?_⟩
    apply Over.OverMorphism.ext
    dsimp only [Over.pullback, Over.homMk, CostructuredArrow.homMk, Over.Hom.left]
    apply pullback.hom_ext
    · simp only [pullback.lift_fst]
      apply (cancel_epi (pullbackSymmetry (X.fromSpecStalk (genericPoint X)) U.hom).hom).mp
      dsimp only [f, Over.homMk, CostructuredArrow.homMk, Over.Hom.left]
      simpa only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc, genericMap] using
        Scheme.extendFromGenericFiber_comp X U.hom Z.hom
          (genericMap X U Z h) (genericMap_over X U Z h)
    · simp only [pullback.lift_snd]
      exact (Over.w h).symm

variable (H : Grp (Over X)) [IsCommMonObj H.X] [IsIntegralHom H.X.hom]

/-- Generic restriction of represented sections is the original pullback of
scheme morphisms, including on non-quasi-compact etale test schemes. -/
theorem isIso_representedBaseChangeUnit :
    IsIso (representedBaseChangeUnit (X.fromSpecStalk (genericPoint X)) H) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have : Etale ((Scheme.Etale.forget X).obj U.unop).hom := U.unop.prop
  have : Smooth ((Scheme.Etale.forget X).obj U.unop).hom := inferInstance
  obtain ⟨hinj, hsurj⟩ := genericPullbackHom_bijective X
    ((Scheme.Etale.forget X).obj U.unop) H.X
  constructor
  · intro a b hab
    apply ULift.ext
    apply Additive.toMul.injective
    apply hinj
    exact congrArg (fun t => t.down.toMul) hab
  · intro b
    obtain ⟨a, ha⟩ := hsurj b.down.toMul
    refine ⟨⟨Additive.ofMul a⟩, ?_⟩
    apply ULift.ext
    exact congrArg Additive.ofMul ha

private theorem isIso_unit_of_leftKanIso {S T : Scheme.{u}} (f : T ⟶ S)
    (L : AbelianSheaf.{u, u + 1} S) (M : AbelianSheaf.{u, u + 1} T)
    (e : (siteBaseChange f).op.lan.obj L.obj ≅ M.obj)
    (α : L.obj ⟶ (siteBaseChange f).op ⋙ M.obj)
    (h : (siteBaseChange f).op.leftKanExtensionUnit L.obj ≫
      Functor.whiskerLeft (siteBaseChange f).op e.hom = α) [IsIso α] :
    IsIso ((inverseImageAdjunction f).unit.app L) :=
  Functor.isIso_unit_of_leftKanIso (siteBaseChange f) AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
    (inverseImageAdjunction f) L M e α h

/-- The original inverse-image adjunction unit is an isomorphism for an integral
etale commutative group scheme over the normal integral base. -/
theorem isIso_representedGenericUnit [Etale H.X.hom] :
    IsIso ((inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit.app
      (representedSheaf H)) := by
  let j := X.fromSpecStalk (genericPoint X)
  have := isIso_representedBaseChangeUnit X H
  apply isIso_unit_of_leftKanIso j (representedSheaf H)
    (representedSheaf (baseChangedGroup j H)) (representedPresheafBaseChangeIso j H)
    (representedBaseChangeUnit j H)
  exact Functor.descOfIsLeftKanExtension_fac _ _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.NormalConstants
