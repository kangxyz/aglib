/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares
/-! # The original derived adjunction unit on localized complexes -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory.Adjunction
universe u v d u' v' d'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{d'} B] [EnoughInjectives B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] [F.PreservesHomology]

/-- The installed adjunction unit retains the original ordinary unit and both derived units. -/
theorem rightDerivedFunctorPlus_unit_eq (adj : F ⊣ G) (K : CochainComplex.Plus A) :
    adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map (adj.mapCochainComplexPlus.unit.app K) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  have h := congrArg (fun z => z ≫ G.rightDerivedFunctorPlus.map
    (F.rightDerivedFunctorPlusExactComparison.inv.app K)) (adj.rightDerivedFunctorPlus_unit_fac K)
  rw [Category.assoc, ← G.rightDerivedFunctorPlus.map_comp, Iso.hom_inv_id_app] at h
  have hm := G.rightDerivedFunctorPlus.map_id
    ((DerivedCategory.Plus.Q (C := A) ⋙ F.rightDerivedFunctorPlus).obj K)
  rw [hm] at h
  have hi := Category.comp_id (adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Q.obj K))
  dsimp only [Functor.comp_obj] at h hi
  rw [hi, rightDerivedFunctorPlusExactComparison_inv_app, Category.assoc] at h
  exact h
end CategoryTheory.Adjunction
