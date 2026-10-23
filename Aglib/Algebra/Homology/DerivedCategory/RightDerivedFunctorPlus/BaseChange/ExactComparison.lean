/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport

/-! # Exact-comparison compatibility with the original functor isomorphisms -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor

universe u v w u' v' w'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]

/-- Transport of exact derived functors respects their original exact comparison. -/
theorem rightDerivedFunctorPlusIso_exactComparison (e : F ≅ G)
    (K : CochainComplex.Plus A) :
    (F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        G.rightDerivedFunctorPlusExactComparison.hom.app K =
      F.rightDerivedFunctorPlusExactComparison.hom.app K ≫
        DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K) := by
  apply (cancel_epi (F.rightDerivedFunctorPlusExactComparison.inv.app K)).mp
  change F.rightDerivedFunctorPlusUnit.app K ≫
      ((F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        G.rightDerivedFunctorPlusExactComparison.hom.app K) = _
  rw [← Category.assoc, F.rightDerivedFunctorPlusIso_hom_app e K, Category.assoc]
  have hG := G.rightDerivedFunctorPlusExactComparison.inv_hom_id_app K
  change G.rightDerivedFunctorPlusUnit.app K ≫
    G.rightDerivedFunctorPlusExactComparison.hom.app K = 𝟙 _ at hG
  rw [hG]
  let q : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) ⟶
      DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj K) :=
    DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K)
  change q ≫ 𝟙 _ = F.rightDerivedFunctorPlusExactComparison.inv.app K ≫
    F.rightDerivedFunctorPlusExactComparison.hom.app K ≫ q
  exact (Category.comp_id q).trans
    (F.rightDerivedFunctorPlusExactComparison.inv_hom_id_app_assoc K q).symm

end CategoryTheory.Functor
