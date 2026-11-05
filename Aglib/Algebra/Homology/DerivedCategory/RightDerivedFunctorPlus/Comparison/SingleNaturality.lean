/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.NaturalTransformation
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare

/-! # Original exact-single comparisons retain arbitrary coefficient transformations -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

omit [HasDerivedCategory.{wA} A] [EnoughInjectives A] [HasDerivedCategory.{wB} B] in
/-- The original complex-single maps intertwine the actual coefficient transformation. -/
theorem mapCochainComplexPlusSingleIso_naturality (α : F ⟶ G) (M : A) :
    (NatTrans.mapCochainComplexPlus α).app ((CochainComplex.singleFunctorPlus A 0).obj M) ≫
        (mapCochainComplexPlusSingleIso G M).hom =
      (mapCochainComplexPlusSingleIso F M).hom ≫
        (CochainComplex.singleFunctorPlus B 0).map (α.app M) := by
  apply ObjectProperty.hom_ext
  change (α.mapHomologicalComplex (.up ℤ)).app
      ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
      (HomologicalComplex.single B (.up ℤ) 0).map (α.app M)
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]

variable [F.PreservesHomology] [G.PreservesHomology]

/-- The native exact-single derived comparison is natural in the whole coefficient functor. -/
theorem rightDerivedFunctorPlusSingleIso_naturality (α : F ⟶ G) :
    whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
        (F.rightDerivedFunctorPlusNatTrans α) ≫
      (G.rightDerivedFunctorPlusSingleIso 0).hom =
    (F.rightDerivedFunctorPlusSingleIso 0).hom ≫
      whiskerRight α (DerivedCategory.Plus.singleFunctor B 0) := by
  apply NatTrans.ext
  funext M
  let K := (CochainComplex.singleFunctorPlus A 0).obj M
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app K)).1
  change F.rightDerivedFunctorPlusUnit.app K ≫
      ((F.rightDerivedFunctorPlusNatTrans α).app (DerivedCategory.Plus.Q.obj K) ≫
        (G.rightDerivedFunctorPlusSingleIso 0).hom.app M) =
    F.rightDerivedFunctorPlusUnit.app K ≫
      ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (α.app M))
  rw [← Category.assoc, F.rightDerivedFunctorPlusNatTrans_app, Category.assoc,
    G.rightDerivedFunctorPlusSingleIso_unit]
  rw [← Category.assoc, F.rightDerivedFunctorPlusSingleIso_unit]
  change DerivedCategory.Plus.Q.map ((NatTrans.mapCochainComplexPlus α).app K) ≫
      DerivedCategory.Plus.Q.map (mapCochainComplexPlusSingleIso G M).hom =
    DerivedCategory.Plus.Q.map (mapCochainComplexPlusSingleIso F M).hom ≫
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus B 0).map (α.app M))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Plus.Q.map (mapCochainComplexPlusSingleIso_naturality α M)

end CategoryTheory.Functor
