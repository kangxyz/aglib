/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Pulling back the actual categorical torsor action through an adjunction

The group image is the existing monoidal image, and the carrier is the actual
right-adjoint image. The original Hom adjunction constructs every action value
and unique transporter. Naturality and the map formula use its actual unit and
counit. No equivariance, action equality or final pullback result is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.TorsorAction

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [CartesianMonoidalCategory D]
  {L : D ⥤ C} {F : C ⥤ D} [F.Monoidal] (adj : L ⊣ F)

/-- The original Hom adjunction preserves the native point-group multiplication. -/
def adjointPointMulEquiv (T : D) (A : Grp C) :
    (L.obj T ⟶ A.X) ≃* (T ⟶ (F.mapGrp.obj A).X) where
  __ := adj.homEquiv T A.X
  map_mul' a b := by
    let : GrpObj (F.obj A.X) := (F.mapGrp.obj A).grp
    change adj.unit.app T ≫ F.map (a * b) =
      (adj.unit.app T ≫ F.map a) * (adj.unit.app T ≫ F.map b)
    rw [F.map_mul, comp_mul]
    rfl

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [F.Monoidal] in
/-- Inverse Hom transport is natural on every actual target test object. -/
theorem homEquiv_symm_naturality {T U : D} (g : T ⟶ U) (Y : C) (x : U ⟶ F.obj Y) :
    (adj.homEquiv T Y).symm (g ≫ x) = L.map g ≫ (adj.homEquiv U Y).symm x :=
  adj.homEquiv_naturality_left_symm g x

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [F.Monoidal] in
/-- The inverse adjoint of an actual mapped arrow is composition with the actual counit. -/
theorem homEquiv_symm_map {U Y : C} (x : U ⟶ Y) :
    (adj.homEquiv (F.obj U) Y).symm (F.map x) = adj.counit.app U ≫ x := by
  change L.map (F.map x) ≫ adj.counit.app Y = _
  exact adj.counit.naturality x

variable (A : Grp C) (Y : C) (τ : TorsorAction A (toUnit Y))

/-- The whole actual image action and transporter, constructed from the one Hom adjunction. -/
def pullback : TorsorAction (F.mapGrp.obj A) (toUnit (F.obj Y)) where
  act {T} a x := adj.homEquiv T Y
    (τ.act ((adjointPointMulEquiv adj T A).symm a) ((adj.homEquiv T Y).symm x))
  naturality {T U} g a x := by
    apply (adj.homEquiv T Y).symm.injective
    rw [homEquiv_symm_naturality, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      τ.naturality]
    congr 1
    · change L.map g ≫ (adj.homEquiv U A.X).symm a =
        (adj.homEquiv T A.X).symm (g ≫ a)
      exact (adj.homEquiv_naturality_left_symm g a).symm
    · exact (adj.homEquiv_naturality_left_symm g x).symm
  one_act {T} x := by
    rw [map_one, τ.one_act, Equiv.apply_symm_apply]
  mul_act {T} a b x := by
    rw [map_mul, τ.mul_act]
    congr 1
    rw [Equiv.symm_apply_apply]
  over _ _ := toUnit_unique _ _
  transport {T} x y _ := by
    obtain ⟨a, ha, hu⟩ := τ.transport ((adj.homEquiv T Y).symm x)
      ((adj.homEquiv T Y).symm y) (toUnit_unique _ _)
    refine ⟨adjointPointMulEquiv adj T A a, ?_, ?_⟩
    · exact (congrArg (fun b => adj.homEquiv T Y
        (τ.act b ((adj.homEquiv T Y).symm x)))
          ((adjointPointMulEquiv adj T A).symm_apply_apply a)).trans
        ((congrArg (adj.homEquiv T Y) ha).trans ((adj.homEquiv T Y).apply_symm_apply y))
    · intro b hb
      apply (adjointPointMulEquiv adj T A).symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply hu
      exact (adj.homEquiv T Y).injective
        (hb.trans ((adj.homEquiv T Y).apply_symm_apply y).symm)

/-- Actual mapped arrows intertwine the same action, by counit naturality. -/
theorem pullback_map {U : C} (a : U ⟶ A.X) (x : U ⟶ Y) :
    (pullback adj A Y τ).act (F.map a) (F.map x) = F.map (τ.act a x) := by
  apply (adj.homEquiv (F.obj U) Y).symm.injective
  change (adj.homEquiv (F.obj U) Y).symm
    ((adj.homEquiv (F.obj U) Y) (τ.act _ _)) = _
  rw [Equiv.symm_apply_apply]
  change τ.act ((adj.homEquiv (F.obj U) A.X).symm (F.map a))
    ((adj.homEquiv (F.obj U) Y).symm (F.map x)) = _
  simp only [homEquiv_symm_map, τ.naturality]

/-- The exact point value under the original Hom equivalence fixes every fibre formula. -/
theorem pullback_homEquiv (T : D) (a : L.obj T ⟶ A.X) (x : L.obj T ⟶ Y) :
    (pullback adj A Y τ).act (adjointPointMulEquiv adj T A a) (adj.homEquiv T Y x) =
      adj.homEquiv T Y (τ.act a x) := by
  change adj.homEquiv T Y (τ.act
    ((adjointPointMulEquiv adj T A).symm (adjointPointMulEquiv adj T A a))
    ((adj.homEquiv T Y).symm (adj.homEquiv T Y x))) = _
  rw [MulEquiv.symm_apply_apply, Equiv.symm_apply_apply]

end CategoryTheory.TorsorAction
