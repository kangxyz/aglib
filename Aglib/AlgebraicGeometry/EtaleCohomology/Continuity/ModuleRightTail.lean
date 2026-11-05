/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleUnderlyingSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleConeCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramRightTail

/-! # Scalar forgetting on the original native right-image tails

Every object, transition and index-equality transport is the original one.
The comparison is identity on the underlying abelian sheaves, without any
fullness assumption or finite additive-carrier restriction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R] {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ)

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

/-- Forgetting the inverse reindexed composition gives the inverse of the
same original abelian comparison. -/
theorem underlying_diagram_compIso_inv {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
    (F : Coefficient R (X.obj k).unop) :
    (underlying R (X.obj i).unop).map
        (((diagramAdjunctionData R X).compIso a b).inv.app F) =
      ((Continuity.diagramAdjunctionData X).compIso a b).inv.app
        ((underlying R (X.obj k).unop).obj F) := by
  apply (cancel_mono (((Continuity.diagramAdjunctionData X).compIso a b).hom.app
    ((underlying R (X.obj k).unop).obj F))).mp
  rw [← underlying_diagram_compIso_hom]
  erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [underlying_diagram_compIso_hom, Iso.inv_hom_id_app]
  rfl

/-- An actual fixed-stage right-image step retains precisely its abelian arrow. -/
theorem underlying_rightStep (F : DiagramCoefficientSystem R X)
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (underlying R (X.obj i).unop).map
        (InjectiveSystem.System.rightStep (diagramAdjunctionData R X) F a b) =
      InjectiveSystem.System.rightStep (Continuity.diagramAdjunctionData X)
        (underlyingSystem R X F) a b := by
  simp only [InjectiveSystem.System.rightStep, Functor.map_comp,
    underlying_diagram_compIso_inv]
  rfl

/-- Equality transport in the original under category also commutes with forgetting. -/
theorem underlying_rightTailTransition (F : DiagramCoefficientSystem R X)
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (t : i ⟶ k) (h : a ≫ b = t) :
    (underlying R (X.obj i).unop).map
        (InjectiveSystem.System.rightTailTransition (diagramAdjunctionData R X) F a b t h) =
      InjectiveSystem.System.rightTailTransition (Continuity.diagramAdjunctionData X)
        (underlyingSystem R X F) a b t h := by
  subst t
  simpa only [InjectiveSystem.System.rightTailTransition, eqToHom_refl,
    Category.comp_id] using underlying_rightStep R X F a b

/-- The original native right-tail diagram becomes the original abelian
right-tail diagram after forgetting scalars. -/
def rightTailUnderlyingIso (F : DiagramCoefficientSystem R X) (i : I) :
    diagramRightTail R X F i ⋙ underlying R (X.obj i).unop ≅
      Continuity.diagramRightTail X (underlyingSystem R X F) i :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change (underlying R (X.obj i).unop).map
      (InjectiveSystem.System.rightTailTransition (diagramAdjunctionData R X) F
        a.hom f.right b.hom (Under.w f)) = _
    exact underlying_rightTailTransition R X F a.hom f.right b.hom (Under.w f))

/-- Original section evaluation retains the original coefficient-forgetting functor. -/
def rightTailSectionsUnderlyingIso (F : DiagramCoefficientSystem R X) (i : I)
    (T : (X.obj i).unop.Etale) :
    diagramRightTail R X F i ⋙
        (sheafSections (X.obj i).unop.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op T) ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ≅
      Continuity.diagramRightTail X (underlyingSystem R X F) i ⋙
        (sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T) :=
  Functor.isoWhiskerRight (rightTailUnderlyingIso R X F i)
    ((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
