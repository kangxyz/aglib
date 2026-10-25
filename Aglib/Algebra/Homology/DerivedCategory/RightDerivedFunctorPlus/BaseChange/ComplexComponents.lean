/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison

/-! # Original exchange components on bounded-below complexes

The actual exchange on complexes retains the original natural transformation
at each term. The native composition maps are normalized while the functors
and original transformation remain abstract, before geometric specialization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)

/-- Every term of the original complex exchange is its original underived component. -/
theorem exchangeOnComplexes_app_f (K : CochainComplex.Plus B) (n : ℤ) :
    ((exchangeOnComplexes R₁ R₂ G H α).app K).hom.f n = α.app (K.obj.X n) := by
  change (𝟙 _ ≫ α.app (K.obj.X n) ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

end CategoryTheory.Functor
