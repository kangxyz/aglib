/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Linear.Adjunction
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Linearity of native sheafification and constant sheaves

The native inclusion of sheaves into presheaves is linear for the existing
pointwise scalar structures. Its actual left adjoint, and hence the original
constant-sheaf functor, are linear for those same structures.
-/

@[expose] public section

namespace CategoryTheory

universe r u v w w'

variable (R : Type r) [Semiring R]
  {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{w'} A] [Preadditive A] [Linear R A]
  [HasWeakSheafify J A]

/-- Native sheafification respects the given pointwise scalar actions. -/
instance presheafToSheaf_linear : (presheafToSheaf J A).Linear R :=
  Adjunction.left_adjoint_linear R (sheafificationAdjunction J A)

/-- The native constant-sheaf functor respects the original coefficient scalars. -/
instance constantSheaf_linear : (constantSheaf J A).Linear R := by
  let : (Functor.const Cᵒᵖ : A ⥤ Cᵒᵖ ⥤ A).Linear R := ⟨fun _ _ => rfl⟩
  unfold constantSheaf
  infer_instance

end CategoryTheory
