/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# The adjunction bijection on points of monoid objects

Let `C` and `D` be cartesian monoidal categories and `adj : L ⊣ R` an adjunction with
`L : C ⥤ D` and `R` monoidal, for example a right adjoint with the monoidal structure induced by
its preservation of finite products. For a monoid object `M` of `D`, `R.obj M` is a monoid object
(Mathlib's `Functor.monObjObj`), and for every object `T` of `C` the adjunction bijection

`(L T ⟶ M) ≃ (T ⟶ R M)`

is an isomorphism of monoids for the convolution monoid structures `Hom.monoid`
(`Adjunction.homMulEquiv`, `Adjunction.homEquiv_mul`, `Adjunction.homEquiv_symm_mul`). Indeed the
bijection is `f ↦ η_T ≫ R.map f`; `R.map` is multiplicative (`Functor.map_mul`) and so is
precomposition (`MonObj.comp_mul`). No hypothesis on `L` is used.

The consumer is the comparison of the group law of a base-changed representing scheme with the
base change of the group law, with `R = Over.pullback g`
(`Aglib.AlgebraicGeometry.Picard.BaseChangeGroupLaw`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Monoidal] {M : D} [MonObj M]

/-- The adjunction bijection `(L T ⟶ M) ≃ (T ⟶ R M)` is multiplicative. -/
theorem homEquiv_mul {T : C} (f g : L.obj T ⟶ M) :
    adj.homEquiv T M (f * g) = adj.homEquiv T M f * adj.homEquiv T M g := by
  rw [adj.homEquiv_unit, adj.homEquiv_unit, adj.homEquiv_unit, Functor.map_mul, MonObj.comp_mul]

/-- The adjunction bijection `(L T ⟶ M) ≃ (T ⟶ R M)` preserves the unit. -/
theorem homEquiv_one (T : C) : adj.homEquiv T M 1 = 1 := by
  rw [adj.homEquiv_unit, Functor.map_one, MonObj.comp_one]

/-- **The adjunction bijection as an isomorphism of monoids**: `(L T ⟶ M) ≃* (T ⟶ R M)`, for a
monoid object `M` of `D` and the monoid object `R.obj M`. -/
def homMulEquiv (T : C) : (L.obj T ⟶ M) ≃* (T ⟶ R.obj M) where
  toEquiv := adj.homEquiv T M
  map_mul' := adj.homEquiv_mul

theorem homMulEquiv_apply {T : C} (f : L.obj T ⟶ M) : adj.homMulEquiv T f = adj.homEquiv T M f :=
  rfl

/-- The inverse adjunction bijection `(T ⟶ R M) ≃ (L T ⟶ M)` is multiplicative. -/
theorem homEquiv_symm_mul {T : C} (f g : T ⟶ R.obj M) :
    (adj.homEquiv T M).symm (f * g) = (adj.homEquiv T M).symm f * (adj.homEquiv T M).symm g :=
  map_mul (adj.homMulEquiv T).symm f g

end CategoryTheory.Adjunction
