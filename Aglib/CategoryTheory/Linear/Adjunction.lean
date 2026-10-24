/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of a left adjoint

If the right adjoint between linear categories is linear, naturality of the
actual adjunction unit identifies the left adjoint's scalar endomorphisms.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe r u v u' v'

variable (R : Type r) [Semiring R]
  {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryTheory.Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj in
/-- A left adjoint to a linear functor is linear for the given category actions. -/
lemma left_adjoint_linear [G.Linear R] : F.Linear R := by
  refine (Functor.linear_iff R F).2 fun X r => ?_
  apply (adj.homEquiv X (F.obj X)).injective
  simp only [homEquiv_apply, adj.unit_naturality, G.map_smul, G.map_id,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  exact congrArg (fun f : X ⟶ (F ⋙ G).obj X => r • f)
    (Category.comp_id (adj.unit.app X)).symm

end CategoryTheory.Adjunction
