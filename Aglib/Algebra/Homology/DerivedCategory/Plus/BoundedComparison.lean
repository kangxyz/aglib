/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.HomotopyCategory.Plus.BoundedComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
/-! # Original triangulated comparison on bounded D+ representatives

Finite brutal layers test an already defined, shift-compatible natural
transformation on bounded complexes. This provides no natural choice of models.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Pretriangulated
namespace DerivedCategory.Plus
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryTheory.Limits.HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : DerivedCategory.Plus A ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G) [τ.CommShift ℤ]

/-- The original natural comparison is invertible on bounded complexes when
it is invertible on their actual original degree-zero single terms. -/
theorem isIso_app_of_term_bounds (K : CochainComplex.Plus A) (a b : ℤ)
    (hl : ∀ n, n < a → CategoryTheory.Limits.IsZero (K.obj.X n))
    (hu : ∀ n, b < n → CategoryTheory.Limits.IsZero (K.obj.X n))
    (hs : ∀ n, IsIso (τ.app ((DerivedCategory.Plus.singleFunctor A 0).obj (K.obj.X n)))) :
    IsIso (τ.app (DerivedCategory.Plus.Q.obj K)) := by
  rw [← NatTrans.isIso_app_iff_of_iso τ ((DerivedCategory.Plus.quotientCompQhIso A).app K)]
  let τh := Functor.whiskerLeft DerivedCategory.Plus.Qh τ
  apply CochainComplex.isIso_app_of_term_bounds τh K a b hl hu
  intro n
  apply CochainComplex.isIso_app_single_of_zero τh (K.obj.X n)
  change IsIso (τ.app ((DerivedCategory.Plus.Qh).obj
    ((HomotopyCategory.Plus.quotient A).obj (CochainComplex.singlePlus (K.obj.X n) 0))))
  exact (NatTrans.isIso_app_iff_of_iso τ
    ((DerivedCategory.Plus.quotientCompQhIso A).app
      (CochainComplex.singlePlus (K.obj.X n) 0))).mpr (hs n)
end DerivedCategory.Plus
