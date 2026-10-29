/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Reduced
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedBaseChange
public import Aglib.CategoryTheory.Sites.Continuous.KanUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Generic detection of represented coefficients on an integral scheme

Etale test schemes over an integral base are reduced, and their literal generic
pullbacks are dominant. Generic restriction therefore detects maps into separated
coefficient schemes. The resulting monomorphism is the original inverse-image
adjunction unit; no normality or Noetherian hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.GenericDetection

universe u

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [IsIntegral X]

/-- The original generic pullback detects maps from an etale test scheme into
any separated scheme over the integral base. -/
theorem genericPullbackHom_injective (U Z : Over X) [Etale U.hom] [IsSeparated Z.hom] :
    Function.Injective (fun h : U ⟶ Z =>
      (Over.pullback (X.fromSpecStalk (genericPoint X))).map h) := by
  have : GeometricallyReduced U.hom := Etale.geometricallyReduced U.hom
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have : IsReduced U.left :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents U.hom
  let j := X.fromSpecStalk (genericPoint X)
  have : IsDominant (pullback.fst U.hom j) := by
    constructor
    change Dense (Set.range (pullback.fst U.hom j))
    rw [Scheme.Pullback.range_fst]
    exact j.denseRange.preimage U.hom.isOpenMap
  intro f g h
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated Z.hom
    ((Over.w f).trans (Over.w g).symm) (pullback.fst U.hom j)
  have hh := congrArg (fun k => k.left ≫ pullback.fst Z.hom j) h
  simpa only [j, Over.pullback_map_left, pullback.lift_fst] using hh

variable (H : Grp (Over X)) [IsCommMonObj H.X] [IsSeparated H.X.hom]

/-- Pullback of actual represented sections to the original generic fibre is
a monomorphism on the full small-etale site. -/
theorem mono_representedBaseChangeUnit :
    Mono (representedBaseChangeUnit (X.fromSpecStalk (genericPoint X)) H) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  have : Etale ((Scheme.Etale.forget X).obj U.unop).hom := U.unop.prop
  intro a b hab
  apply ULift.ext
  apply Additive.toMul.injective
  apply genericPullbackHom_injective X ((Scheme.Etale.forget X).obj U.unop) H.X
  exact congrArg (fun t => t.down.toMul) hab

private theorem mono_unit_of_leftKanIso {S T : Scheme.{u}} (f : T ⟶ S)
    (L : AbelianSheaf.{u, u + 1} S) (M : AbelianSheaf.{u, u + 1} T)
    (e : (siteBaseChange f).op.lan.obj L.obj ≅ M.obj)
    (α : L.obj ⟶ (siteBaseChange f).op ⋙ M.obj)
    (h : (siteBaseChange f).op.leftKanExtensionUnit L.obj ≫
      Functor.whiskerLeft (siteBaseChange f).op e.hom = α) [Mono α] :
    Mono ((inverseImageAdjunction f).unit.app L) :=
  Functor.mono_unit_of_leftKanIso (siteBaseChange f) AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
    (inverseImageAdjunction f) L M e α h

/-- The actual generic adjunction unit is monic for separated etale represented
abelian coefficients over every integral base. -/
theorem mono_representedGenericUnit [Etale H.X.hom] :
    Mono ((inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit.app
      (representedSheaf H)) := by
  let j := X.fromSpecStalk (genericPoint X)
  have := mono_representedBaseChangeUnit X H
  apply mono_unit_of_leftKanIso j (representedSheaf H)
    (representedSheaf (baseChangedGroup j H)) (representedPresheafBaseChangeIso j H)
    (representedBaseChangeUnit j H)
  exact Functor.descOfIsLeftKanExtension_fac _ _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.GenericDetection
