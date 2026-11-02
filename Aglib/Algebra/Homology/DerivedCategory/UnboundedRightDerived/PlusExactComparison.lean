/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactSquare
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquare

/-! # Exact localization factors across bounded-below inclusion -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The inverse fixed plus/full comparison retains the original exact factors. -/
theorem rightDerivedFunctorPlusCompιIso_inv_exactComparison (K : CochainComplex.Plus C) :
    F.rightDerivedFunctorPlusCompιIso.inv.app (DerivedCategory.Plus.Q.obj K) ≫
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusExactComparison.hom.app K) =
      F.mapDerivedCategoryFactors.hom.app K.obj := by
  have h : DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) =
      F.mapDerivedCategoryFactors.inv.app K.obj := by
    simpa using F.rightDerivedFunctorPlusCompιIso_unit K
  have hk : DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusExactComparison.hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp]
    change DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusExactComparison.inv.app K ≫
        F.rightDerivedFunctorPlusExactComparison.hom.app K) = _
    rw [Iso.inv_hom_id_app, DerivedCategory.Plus.ι.map_id]
  apply (cancel_epi (F.mapDerivedCategoryFactors.inv.app K.obj)).mp
  calc
    _ = (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K)) ≫
        (F.rightDerivedFunctorPlusCompιIso.inv.app (DerivedCategory.Plus.Q.obj K) ≫
          DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusExactComparison.hom.app K)) :=
      congrArg (fun z => z ≫ _) h.symm
    _ = 𝟙 _ := by
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hk
    _ = _ := (F.mapDerivedCategoryFactors.inv_hom_id_app K.obj).symm

end CategoryTheory.Functor
