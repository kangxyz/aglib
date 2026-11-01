/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.TripleLocalization
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.UnitExpansion
/-! # The original canonical outer-adjoint map after deriving -/
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
  (t : Triple J U S) (e : J ≅ S)
  (he : ∀ X, e.hom.app X ≫ S.map (t.adj₁.unit.app X) = t.adj₂.unit.app (J.obj X))

include he in
/-- Native deriving preserves the original canonical outer-adjoint comparison. -/
theorem Triple.rightDerivedFunctorPlus_leftToRight :
    (show Triple J.rightDerivedFunctorPlus U.rightDerivedFunctorPlus S.rightDerivedFunctorPlus
      from ⟨t.adj₁.rightDerivedFunctorPlus, t.adj₂.rightDerivedFunctorPlus⟩).leftToRight =
        (J.rightDerivedFunctorPlusIso e).hom := by
  apply J.rightDerivedFunctorPlus.rightDerived_ext J.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app]
  rw [rightDerivedFunctorPlusIso_hom_app]
  apply Triple.leftToRight_normalized
    (show Triple J.mapCochainComplexPlus U.mapCochainComplexPlus S.mapCochainComplexPlus
      from ⟨t.adj₁.mapCochainComplexPlus, t.adj₂.mapCochainComplexPlus⟩)
    (show Triple J.rightDerivedFunctorPlus U.rightDerivedFunctorPlus S.rightDerivedFunctorPlus
      from ⟨t.adj₁.rightDerivedFunctorPlus, t.adj₂.rightDerivedFunctorPlus⟩)
    DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    J.rightDerivedFunctorPlusUnit U.rightDerivedFunctorPlusUnit S.rightDerivedFunctorPlusUnit
    t.adj₁.rightDerivedFunctorPlus_unit_eq t.adj₂.rightDerivedFunctorPlus_unit_eq
    (NatIso.mapCochainComplexPlus e).hom
  intro L
  apply ObjectProperty.hom_ext
  ext n
  change e.hom.app (L.obj.X n) ≫ S.map (t.adj₁.unit.app (L.obj.X n)) =
    t.adj₂.unit.app (J.obj (L.obj.X n))
  exact he (L.obj.X n)
end CategoryTheory.Adjunction
