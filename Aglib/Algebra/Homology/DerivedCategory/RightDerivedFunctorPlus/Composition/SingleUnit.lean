/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Acyclic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison

/-!
# Composition of the original right-derived single units

The existing native single unit commutes with the original composition
comparison and with the original derived isomorphism comparison. No second
single-unit model or exactness hypothesis is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    [EnoughInjectives A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [EnoughInjectives B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- Composition of the actual native single units, through the original
comparison on the original coefficient single. No comparison is assumed invertible. -/
@[reassoc]
theorem rightDerivedSingleUnit_comp (M : A) :
    (F ⋙ G).rightDerivedSingleUnit M ≫
        (rightDerivedFunctorPlusCompComparison F G).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      G.rightDerivedSingleUnit (F.obj M) ≫ G.rightDerivedFunctorPlus.map
        (F.rightDerivedSingleUnit M) := by
  let K := (CochainComplex.singleFunctorPlus A 0).obj M
  let L := (CochainComplex.singleFunctorPlus B 0).obj (F.obj M)
  let N := (CochainComplex.singleFunctorPlus C 0).obj (G.obj (F.obj M))
  let Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C := DerivedCategory.Plus.Q
  let QB : CochainComplex.Plus B ⥤ DerivedCategory.Plus B := DerivedCategory.Plus.Q
  let τF : L ⟶ F.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let τG : N ⟶ G.mapCochainComplexPlus.obj L :=
    ObjectProperty.homMk ((singleMapHomologicalComplex G (.up ℤ) 0).inv.app (F.obj M))
  let τFG : N ⟶ (F ⋙ G).mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex (F ⋙ G) (.up ℤ) 0).inv.app M)
  have hτ : τFG = τG ≫ G.mapCochainComplexPlus.map τF := by
    apply ObjectProperty.hom_ext
    exact singleMapHomologicalComplex_comp_inv_app F G (.up ℤ) (0 : ℤ) M
  change (Q.map τFG ≫ (F ⋙ G).rightDerivedFunctorPlusUnit.app K) ≫
      (rightDerivedFunctorPlusCompComparison F G).app (DerivedCategory.Plus.Q.obj K) =
    (Q.map τG ≫ G.rightDerivedFunctorPlusUnit.app L) ≫
      G.rightDerivedFunctorPlus.map (QB.map τF ≫ F.rightDerivedFunctorPlusUnit.app K)
  erw [Category.assoc, rightDerivedFunctorPlusCompComparison_app, hτ,
    Q.map_comp, G.rightDerivedFunctorPlus.map_comp]
  have hn := congrArg (fun z => Q.map τG ≫ z ≫
    G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K))
    (G.rightDerivedFunctorPlusUnit.naturality τF)
  simp only [Functor.comp_map, Category.assoc] at hn
  convert hn using 1
  all_goals first | rfl | exact Category.assoc _ _ _

omit [EnoughInjectives B] in
/-- The original single unit retains an original ordinary functor isomorphism
and the native derived isomorphism induced by that same isomorphism. -/
@[reassoc]
theorem rightDerivedSingleUnit_iso_hom {F' : A ⥤ B} [F'.Additive]
    (e : F ≅ F') (M : A) :
    (DerivedCategory.Plus.singleFunctor B 0).map (e.hom.app M) ≫
        F'.rightDerivedSingleUnit M =
      F.rightDerivedSingleUnit M ≫ (F.rightDerivedFunctorPlusIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
  let K := (CochainComplex.singleFunctorPlus A 0).obj M
  let S := CochainComplex.singleFunctorPlus B 0
  let Q : CochainComplex.Plus B ⥤ DerivedCategory.Plus B := DerivedCategory.Plus.Q
  let τ : S.obj (F.obj M) ⟶ F.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let τ' : S.obj (F'.obj M) ⟶ F'.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F' (.up ℤ) 0).inv.app M)
  let eK := (NatIso.mapCochainComplexPlus e).hom.app K
  have hτ : S.map (e.hom.app M) ≫ τ' = τ ≫ eK := by
    apply ObjectProperty.hom_ext
    change (single B (.up ℤ) 0).map (e.hom.app M) ≫
        (singleMapHomologicalComplex F' (.up ℤ) 0).inv.app M =
      (singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
        (e.hom.mapHomologicalComplex (.up ℤ)).app ((single A (.up ℤ) 0).obj M)
    rw [natTransMapHomologicalComplex_app_single_obj]
    simp only [Iso.inv_hom_id_app_assoc]
  change Q.map (S.map (e.hom.app M)) ≫
      (Q.map τ' ≫ F'.rightDerivedFunctorPlusUnit.app K) =
    (Q.map τ ≫ F.rightDerivedFunctorPlusUnit.app K) ≫
      (F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K)
  erw [Category.assoc, rightDerivedFunctorPlusIso_hom_app,
    ← Category.assoc, ← Q.map_comp, hτ, Q.map_comp, Category.assoc]

end CategoryTheory.Functor
