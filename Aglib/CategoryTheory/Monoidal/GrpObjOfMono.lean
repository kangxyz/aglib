/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Monoid and group objects on monomorphisms closed under the operations

Let `j : H ⟶ G` be a monomorphism into a monoid object `G` of a monoidal category. If the unit of
`G` and the multiplication `(j ⊗ₘ j) ≫ μ[G]` factor through `j`, the factorizations `one` and
`mul` form a monoid object structure on `H` (`CategoryTheory.MonObj.ofMono`), and `j` is a
monoid morphism (`CategoryTheory.MonObj.isMonHom_ofMono`). In a cartesian monoidal category, if
`G` is a group object and moreover `j ≫ ι[G]` factors through `j`, then `H` is a group object
(`CategoryTheory.GrpObj.ofMono`). Each axiom for `H` follows from the axiom for `G` after
cancelling the monomorphism `j`.

This is the categorical step that makes a subscheme of a group scheme closed under the group law
a group scheme, for example the identity component of a group scheme locally of finite type over
a field (`Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

universe v u

variable {C : Type u} [Category.{v} C]

namespace MonObj

variable [MonoidalCategory C] {G H : C} [MonObj G] (j : H ⟶ G) [Mono j] (one : 𝟙_ C ⟶ H)
  (mul : H ⊗ H ⟶ H) (h_one : one ≫ j = η[G]) (h_mul : mul ≫ j = (j ⊗ₘ j) ≫ μ[G])

/-- **The monoid object structure on a monomorphism closed under the unit and the
multiplication.** -/
@[instance_reducible]
def ofMono : MonObj H where
  one := one
  mul := mul
  one_mul := by
    rw [← cancel_mono j, Category.assoc, h_mul, whiskerRight_comp_tensorHom_assoc, h_one,
      tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
  mul_one := by
    rw [← cancel_mono j, Category.assoc, h_mul, whiskerLeft_comp_tensorHom_assoc, h_one,
      tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
  mul_assoc := by
    rw [← cancel_mono j]
    simp only [Category.assoc, h_mul]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc, h_mul,
      ← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft]
    simp only [Category.assoc]
    rw [MonObj.mul_assoc, associator_naturality_assoc]

/-- The unit of `MonObj.ofMono`. -/
theorem ofMono_one : (ofMono j one mul h_one h_mul).one = one := rfl

/-- The multiplication of `MonObj.ofMono`. -/
theorem ofMono_mul : (ofMono j one mul h_one h_mul).mul = mul := rfl

/-- The monomorphism is a monoid morphism for `MonObj.ofMono`. -/
theorem isMonHom_ofMono : letI := ofMono j one mul h_one h_mul; IsMonHom j :=
  letI := ofMono j one mul h_one h_mul
  { one_hom := h_one
    mul_hom := h_mul }

end MonObj

namespace GrpObj

variable [CartesianMonoidalCategory C] {G H : C} [GrpObj G] (j : H ⟶ G) [Mono j]
  (one : 𝟙_ C ⟶ H) (mul : H ⊗ H ⟶ H) (inv : H ⟶ H) (h_one : one ≫ j = η[G])
  (h_mul : mul ≫ j = (j ⊗ₘ j) ≫ μ[G]) (h_inv : inv ≫ j = j ≫ ι[G])

/-- **The group object structure on a monomorphism closed under the unit, the multiplication and
the inverse.** -/
@[instance_reducible]
def ofMono : GrpObj H where
  toMonObj := MonObj.ofMono j one mul h_one h_mul
  inv := inv
  left_inv := by
    change lift inv (𝟙 H) ≫ mul = toUnit H ≫ one
    rw [← cancel_mono j, Category.assoc, Category.assoc, h_mul, h_one, lift_map_assoc, h_inv,
      Category.id_comp, ← comp_toUnit_assoc j, ← GrpObj.left_inv G, comp_lift_assoc,
      Category.comp_id]
  right_inv := by
    change lift (𝟙 H) inv ≫ mul = toUnit H ≫ one
    rw [← cancel_mono j, Category.assoc, Category.assoc, h_mul, h_one, lift_map_assoc, h_inv,
      Category.id_comp, ← comp_toUnit_assoc j, ← GrpObj.right_inv G, comp_lift_assoc,
      Category.comp_id]

/-- The monoid object underlying `GrpObj.ofMono`. -/
theorem ofMono_toMonObj :
    (ofMono j one mul inv h_one h_mul h_inv).toMonObj = MonObj.ofMono j one mul h_one h_mul :=
  rfl

/-- The inverse of `GrpObj.ofMono`. -/
theorem ofMono_inv : (ofMono j one mul inv h_one h_mul h_inv).inv = inv := rfl

/-- The monomorphism is a monoid morphism for `GrpObj.ofMono`. -/
theorem isMonHom_ofMono : letI := ofMono j one mul inv h_one h_mul h_inv; IsMonHom j :=
  MonObj.isMonHom_ofMono j one mul h_one h_mul

end GrpObj

end CategoryTheory
