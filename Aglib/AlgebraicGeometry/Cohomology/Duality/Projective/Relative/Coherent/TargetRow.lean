/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Boundary.Shift
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# The degree-zero left edge of the target coefficient row

An upper bound on the source, rather than injectivity of coefficients or an
Ext-vanishing claim over the base, gives the left edge of the target sequence.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An upper-bounded source makes the degree-zero shifted coefficient row left exact. -/
theorem coyoneda_shifted_singleTriangle_zero_injective
    (n : ℤ) (K : DerivedCategory C) [K.IsLE n]
    {S : ShortComplex C} (hS : S.ShortExact) :
    let T := (Triangle.shiftFunctor (DerivedCategory C) (-n)).obj hS.singleTriangle
    Function.Injective (((preadditiveCoyoneda.obj (Opposite.op K)).shift (0 : ℤ)).map
      T.mor₁).hom := by
  let T := (Triangle.shiftFunctor (DerivedCategory C) (-n)).obj hS.singleTriangle
  have hT : T ∈ distTriang (DerivedCategory C) :=
    Triangle.shift_distinguished _ hS.singleTriangle_distinguished _
  let H := preadditiveCoyoneda.obj (Opposite.op K)
  have : Mono ((H.shift (0 : ℤ)).map T.mor₁) := by
    apply (H.homologySequence_mono_shift_map_mor₁_iff T hT (-1) 0 (by omega)).mpr
    ext z
    have hz : z = 0 := by
      let : T.obj₃.IsGE n :=
        TStructure.t.isGE_shift ((singleFunctor C 0).obj S.X₃) 0 (-n) n (by omega)
      let : (T.obj₃⟦(-1 : ℤ)⟧).IsGE (n + 1) :=
        TStructure.t.isGE_shift T.obj₃ n (-1) (n + 1) (by omega)
      exact TStructure.t.zero z n (n + 1) (by omega)
    simp only [hz, map_zero]
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

end DerivedCategory
