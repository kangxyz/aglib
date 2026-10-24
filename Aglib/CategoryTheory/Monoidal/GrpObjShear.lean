/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The shear automorphism of a group object

Let `G` be a group object of a cartesian monoidal category. The shear automorphism
`CategoryTheory.GrpObj.shearIso G : G ⊗ G ≅ G ⊗ G` is `(a, b) ↦ (a b⁻¹, b)`, with inverse
`(c, b) ↦ (c b, b)`, written with the group structure on morphisms into `G`
(`fst G G / snd G G` and `fst G G * snd G G`). Followed by the first projection it is the
division map `fst G G / snd G G` (`CategoryTheory.GrpObj.shearIso_hom_fst`). So the division
map, and likewise the multiplication, is a projection up to an automorphism (the diagram in the
proof of Stacks Project, Tag 047K).

Consumer: the openness of the division map of a group scheme over a field
(`Aglib.AlgebraicGeometry.Group.IdentityComponent.QuasiCompact`).
-/

@[expose] public section

namespace CategoryTheory.GrpObj

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

/-- **The shear automorphism** `(a, b) ↦ (a b⁻¹, b)` of `G ⊗ G`, with inverse
`(c, b) ↦ (c b, b)`. -/
def shearIso : G ⊗ G ≅ G ⊗ G where
  hom := lift (fst G G / snd G G) (snd G G)
  inv := lift (fst G G * snd G G) (snd G G)
  hom_inv_id := by
    ext1 <;> simp [MonObj.comp_mul]
  inv_hom_id := by
    ext1 <;> simp [GrpObj.comp_div]

/-- The shear followed by the first projection is the division map. -/
@[reassoc (attr := simp)]
theorem shearIso_hom_fst : (shearIso G).hom ≫ fst G G = fst G G / snd G G :=
  lift_fst _ _

/-- The shear keeps the second coordinate. -/
@[reassoc (attr := simp)]
theorem shearIso_hom_snd : (shearIso G).hom ≫ snd G G = snd G G :=
  lift_snd _ _

end CategoryTheory.GrpObj
