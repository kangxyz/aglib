/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Preadditive

/-! # A complete module diagram from its original coefficient action

An additive coefficient functor and an action on its coefficient object produce
one module-valued diagram. The underlying groups and index maps are the original
ones. All scalar actions come from the same coefficient natural transformations.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v i j w r

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {I : Type i} [Category.{j} I]
  (H : C ⥤ I ⥤ AddCommGrpCat.{w}) [H.Additive]
  {R : Type r} [Ring R] (A : C) (ρ : R →+* End A)

/-- The original coefficient endomorphisms act on each unchanged group. -/
def coefficientScalarAction (i : I) : R →+* AddMonoid.End ((H.obj A).obj i) where
  toFun a := ((H.map (ρ a)).app i).hom
  map_zero' := by
    ext x
    change (H.map (ρ 0)).app i x = 0
    rw [ρ.map_zero, H.map_zero]
    rfl
  map_one' := by
    ext x
    change (H.map (ρ 1)).app i x = x
    rw [ρ.map_one]
    change (H.map (𝟙 A)).app i x = x
    rw [H.map_id]
    rfl
  map_add' a b := by
    ext x
    change (H.map (ρ (a + b))).app i x =
      (H.map (ρ a)).app i x + (H.map (ρ b)).app i x
    rw [ρ.map_add, H.map_add]
    rfl
  map_mul' a b := by
    ext x
    change (H.map (ρ (a * b))).app i x =
      (H.map (ρ a)).app i ((H.map (ρ b)).app i x)
    rw [ρ.map_mul]
    change (H.map (ρ b ≫ ρ a)).app i x = _
    rw [H.map_comp]
    rfl

/-- The specified action on the original group, without a new underlying model. -/
abbrev coefficientModule (i : I) : Module R ((H.obj A).obj i) :=
  Module.compHom _ (H.coefficientScalarAction A ρ i)

/-- Construct the complete original module diagram and all its index laws. -/
def coefficientModuleDiagram : I ⥤ ModuleCat.{w} R where
  obj i := by
    letI := H.coefficientModule A ρ i
    exact ModuleCat.of R ((H.obj A).obj i)
  map {i j} f := by
    letI := H.coefficientModule A ρ i
    letI := H.coefficientModule A ρ j
    refine ModuleCat.ofHom { __ := ((H.obj A).map f).hom, map_smul' := ?_ }
    intro a x
    exact (ConcreteCategory.congr_hom ((H.map (ρ a)).naturality f) x).symm
  map_id i := by
    apply (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).map_injective
    exact (H.obj A).map_id i
  map_comp f g := by
    apply (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).map_injective
    exact (H.obj A).map_comp f g

/-- Forgetting the scalar action recovers the same complete original diagram. -/
def coefficientModuleDiagramForgetIso :
    H.coefficientModuleDiagram A ρ ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ≅ H.obj A :=
  Iso.refl _

/-- Scalars are the original coefficient map at every index. -/
theorem coefficientModuleDiagram_smul (i : I) (a : R) (x : (H.obj A).obj i) :
    letI := H.coefficientModule A ρ i
    a • x = (H.map (ρ a)).app i x := rfl

/-- Every enriched index map retains its original underlying additive map. -/
theorem coefficientModuleDiagram_map_apply {i j : I} (f : i ⟶ j) (x : (H.obj A).obj i) :
    (H.coefficientModuleDiagram A ρ).map f x = (H.obj A).map f x := rfl

end CategoryTheory.Functor
