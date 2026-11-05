/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Sheaf

/-! # Internal torsion through original sheaf isomorphisms

Only the actual underlying presheaf and sectionwise inverse are needed.
No sheafification model is part of this invariance statement.
-/

@[expose] public section
namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An original sheaf isomorphism preserves internal torsion without selecting
any sheafification functor or abelian-category instance. -/
theorem IsTorsion.of_iso {F G : Sheaf J AddCommGrpCat.{w}}
    (hG : IsTorsion G) (e : F ≅ G) : IsTorsion F := by
  apply Presheaf.IsLocallyTorsion.of_injective hG e.hom.hom
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

end CategoryTheory.Sheaf
