/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Divisibility

/-!
# Divisibility after applying a derived functor to a truncation

The actual distinguished truncation triangle transfers divisibility to the
low truncation. No acyclicity assumption on the higher homology objects is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe u v w u' v' w'

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- Native truncation transfer through an additive triangulated functor. The two
middle-object hypotheses are in consecutive degrees; all tail hypotheses are
on the original homology before applying the functor. -/
theorem isIso_nsmul_id_homology_functor_truncLT
    (F : Plus C ⥤ Plus D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (K : Plus C) (a : ℤ) (n : ℕ)
    (hn : ∀ k : ℤ, a ≤ k → IsIso (n • 𝟙 ((homologyFunctor C k).obj K)))
    (i j : ℤ) (hij : i + 1 = j)
    [IsIso (n • 𝟙 ((homologyFunctor D i).obj (F.obj K)))]
    [IsIso (n • 𝟙 ((homologyFunctor D j).obj (F.obj K)))] :
    IsIso (n • 𝟙 ((homologyFunctor D j).obj
      (F.obj ((TStructure.t.truncLT a).obj K)))) := by
  let : IsIso (n • 𝟙 ((TStructure.t.truncGE a).obj K)) :=
    isIso_nsmul_id_truncGE K a n hn
  let : IsIso (n • 𝟙 ((homologyFunctor D i).obj
      (F.obj ((TStructure.t.truncGE a).obj K)))) :=
    isIso_nsmul_id_functor_obj (F ⋙ homologyFunctor D i) _ n
  let : IsIso (n • 𝟙 ((homologyFunctor D j).obj
      (F.obj ((TStructure.t.truncGE a).obj K)))) :=
    isIso_nsmul_id_functor_obj (F ⋙ homologyFunctor D j) _ n
  let T := F.mapTriangle.obj ((TStructure.t.triangleLTGE a).obj K)
  let : IsIso (n • 𝟙 ((homologyFunctor D i).obj T.obj₂)) := by
    change IsIso (n • 𝟙 ((homologyFunctor D i).obj (F.obj K)))
    infer_instance
  let : IsIso (n • 𝟙 ((homologyFunctor D j).obj T.obj₂)) := by
    change IsIso (n • 𝟙 ((homologyFunctor D j).obj (F.obj K)))
    infer_instance
  let : IsIso (n • 𝟙 ((homologyFunctor D i).obj T.obj₃)) := by
    change IsIso (n • 𝟙 ((homologyFunctor D i).obj
      (F.obj ((TStructure.t.truncGE a).obj K))))
    infer_instance
  let : IsIso (n • 𝟙 ((homologyFunctor D j).obj T.obj₃)) := by
    change IsIso (n • 𝟙 ((homologyFunctor D j).obj
      (F.obj ((TStructure.t.truncGE a).obj K))))
    infer_instance
  exact isIso_nsmul_id_homology_obj₁
    (F.mapTriangle.obj ((TStructure.t.triangleLTGE a).obj K))
    (F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished a K)) i j hij n

end DerivedCategory.Plus
