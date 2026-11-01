/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.TripleLocalization
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.UnitExpansion

/-! # The original canonical outer-adjoint map retains its derived unit without invertibility -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory.Adjunction
universe u v d u' v' d'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{d'} B] [EnoughInjectives B]
  {J S : A ⥤ B} {U : B ⥤ A} [J.Additive] [U.Additive] [S.Additive]
  [J.PreservesHomology] [U.PreservesHomology]
  [J.rightDerivedFunctorPlus.Full] [J.rightDerivedFunctorPlus.Faithful]
  (t : Triple J U S) (b : J ⟶ S)
  (hb : ∀ X, b.app X ≫ S.map (t.adj₁.unit.app X) = t.adj₂.unit.app (J.obj X))

include hb in
/-- The actual canonical derived map satisfies the original unit equation for an arbitrary map. -/
theorem Triple.rightDerivedFunctorPlus_leftToRight_unit (K : CochainComplex.Plus A) :
    J.rightDerivedFunctorPlusUnit.app K ≫
      (show Triple J.rightDerivedFunctorPlus U.rightDerivedFunctorPlus S.rightDerivedFunctorPlus
        from ⟨t.adj₁.rightDerivedFunctorPlus, t.adj₂.rightDerivedFunctorPlus⟩).leftToRight.app
        (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((NatTrans.mapCochainComplexPlus b).app K) ≫
        S.rightDerivedFunctorPlusUnit.app K := by
  apply Triple.leftToRight_normalized
    (show Triple J.mapCochainComplexPlus U.mapCochainComplexPlus S.mapCochainComplexPlus
      from ⟨t.adj₁.mapCochainComplexPlus, t.adj₂.mapCochainComplexPlus⟩)
    (show Triple J.rightDerivedFunctorPlus U.rightDerivedFunctorPlus S.rightDerivedFunctorPlus
      from ⟨t.adj₁.rightDerivedFunctorPlus, t.adj₂.rightDerivedFunctorPlus⟩)
    DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    J.rightDerivedFunctorPlusUnit U.rightDerivedFunctorPlusUnit S.rightDerivedFunctorPlusUnit
    t.adj₁.rightDerivedFunctorPlus_unit_eq t.adj₂.rightDerivedFunctorPlus_unit_eq
    (NatTrans.mapCochainComplexPlus b)
  intro L
  apply ObjectProperty.hom_ext
  ext n
  exact hb (L.obj.X n)
end CategoryTheory.Adjunction
