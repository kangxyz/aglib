/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FiniteProducts
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Base change of finite native over-products

The comparison uses the original binary product comparisons of `Over.pullback`.
The empty-family comparison is the native pullback of the actual identity map.
Every original component projection and the original map to the base are retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- The sole finite native over-product commutes with actual base change. -/
def finiteProductOverPullbackIso (f : T ⟶ S) : {n : ℕ} → (X : Fin n → Over S) →
    (Over.pullback f).obj (finiteProductOver X) ≅
      finiteProductOver (fun i => (Over.pullback f).obj (X i))
  | 0, _ => Over.isoMk (asIso (pullback.snd (𝟙 S) f)) (by simp)
  | n + 1, X =>
    asIso (prodComparison (Over.pullback f) (X 0)
      (finiteProductOver (fun i : Fin n => X i.succ))) ≪≫
      prod.mapIso (Iso.refl _) (finiteProductOverPullbackIso f (fun i : Fin n => X i.succ))

@[simp]
theorem finiteProductOverPullbackIso_zero_hom_left (f : T ⟶ S) (X : Fin 0 → Over S) :
    (finiteProductOverPullbackIso f X).hom.left = pullback.snd (𝟙 S) f := rfl

/-- The comparison carries each original component projection to its original base change. -/
@[reassoc (attr := simp)]
theorem finiteProductOverPullbackIso_hom_π (f : T ⟶ S) {n : ℕ} (X : Fin n → Over S)
    (i : Fin n) :
    (finiteProductOverPullbackIso f X).hom ≫
        finiteProductOverπ (fun j => (Over.pullback f).obj (X j)) i =
      (Over.pullback f).map (finiteProductOverπ X i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [finiteProductOverPullbackIso]
    | succ i => simp [finiteProductOverPullbackIso, ih, Functor.map_comp]

/-- The inverse comparison preserves the same original component projections. -/
@[reassoc (attr := simp)]
theorem finiteProductOverPullbackIso_inv_map_π (f : T ⟶ S) {n : ℕ} (X : Fin n → Over S)
    (i : Fin n) :
    (finiteProductOverPullbackIso f X).inv ≫
        (Over.pullback f).map (finiteProductOverπ X i) =
      finiteProductOverπ (fun j => (Over.pullback f).obj (X j)) i := by
  rw [← finiteProductOverPullbackIso_hom_π f X i, Iso.inv_hom_id_assoc]

/-- The underlying scheme map commutes with the actual structure map to the new base. -/
@[reassoc (attr := simp)]
theorem finiteProductOverPullbackIso_hom_base (f : T ⟶ S) {n : ℕ} (X : Fin n → Over S) :
    (finiteProductOverPullbackIso f X).hom.left ≫
        (finiteProductOver (fun i => (Over.pullback f).obj (X i))).hom =
      pullback.snd (finiteProductOver X).hom f :=
  (finiteProductOverPullbackIso f X).hom.w

/-- On schemes, the projection formula retains the original pullback first projections. -/
@[reassoc (attr := simp)]
theorem finiteProductOverPullbackIso_hom_π_fst (f : T ⟶ S) {n : ℕ} (X : Fin n → Over S)
    (i : Fin n) :
    (finiteProductOverPullbackIso f X).hom.left ≫
        (finiteProductOverπ (fun j => (Over.pullback f).obj (X j)) i).left ≫
          pullback.fst (X i).hom f =
      pullback.fst (finiteProductOver X).hom f ≫ (finiteProductOverπ X i).left := by
  rw [← Over.comp_left_assoc, finiteProductOverPullbackIso_hom_π]
  simp [Over.pullback_map_left]

end AlgebraicGeometry.Scheme
