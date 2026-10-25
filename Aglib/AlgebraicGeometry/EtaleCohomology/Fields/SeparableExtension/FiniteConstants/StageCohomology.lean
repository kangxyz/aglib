/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCohomologyCocone
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-! # Actual classes and relations descend along qcqs scheme limits -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u e

attribute [local instance] hasSheafifyLarge

open Continuity

private theorem concreteGroup_exists_relation
    {J : Type u} [Category.{u} J] [IsFiltered J] (D : J ⥤ AddCommGrpCat.{e})
    [PreservesColimit D (CategoryTheory.forget AddCommGrpCat.{e})]
    (C : Cocone D) (hC : IsColimit C) {i j : J}
    (a : D.obj i) (a' : D.obj j)
    (h : (C.ι.app i).hom a = (C.ι.app j).hom a') :
    ∃ (t : J) (f : i ⟶ t) (g : j ⟶ t),
      (D.map f).hom a = (D.map g).hom a' := by
  exact Concrete.isColimit_exists_of_rep_eq (C := AddCommGrpCat.{e})
    (FC := fun A B : AddCommGrpCat.{e} => A →+ B)
    (CC := fun A : AddCommGrpCat.{e} => (A : Type e))
    (D := C) (i := i) (j := j) D hC a a' h

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (b : Cone X) (c : Cocone X) (hc : IsColimit c)
  (l : b.pt ⟶ c.pt) (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  (F : AbelianSheaf.{u, u + 1} b.pt.unop)
  [∀ i, CompactSpace (X.obj i).unop]
  [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [HasColimitsOfShape I AddCommGrpCat.{e}] [UnivLE.{u, e}]

local instance : IsConnected I := IsFiltered.isConnected I

/-- Scheme-limit continuity with the original structural inverse image as apex. -/
def isColimitPullbackCohomologyCocone (q : ℕ) :
    IsColimit (pullbackLimitCohomologyCocone X b c l hl F q) := by
  let E : AddCommGrpCat.of (Sheaf.H.{e}
      (colimit (coneCoefficientFunctor X c (pullbackCoefficientSystem X b F))) q) ≅
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage l.unop).obj F) q) :=
    pullbackLimitCohomologyIso X b c l hl F q
  change IsColimit ((diagramCohomologyCocone X c (pullbackCoefficientSystem X b F) q).extend
    E.hom)
  exact @IsColimit.extendIso I _ AddCommGrpCat.{e} _
    (diagramCohomologyFunctor X (pullbackCoefficientSystem X b F) q)
    (diagramCohomologyCocone X c (pullbackCoefficientSystem X b F) q) _
    E.hom (inferInstance : IsIso E.hom)
    (isColimitDiagramCohomologyOfQcqsStages X c hc
      (pullbackCoefficientSystem X b F) q)

include hc in
/-- Every class is the complete original transfer of a class at one actual stage. -/
theorem exists_stage_cohomologyClass (q : ℕ)
    (a : Sheaf.H.{e} ((inverseImage l.unop).obj F) q) :
    ∃ (i : I) (aᵢ : Sheaf.H.{e} ((inverseImage (b.π.app i).unop).obj F) q),
      cohomologyTransfer (X := (X.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop
        ((pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
          (congrArg Quiver.Hom.unop (hl i))).inv.app F) q aᵢ = a := by
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{e}) :=
    preservesFilteredColimitsOfSize_of_univLE.{e, e, u, u} _
  obtain ⟨i, aᵢ, haᵢ⟩ := Concrete.isColimit_exists_rep
    (diagramCohomologyFunctor X (pullbackCoefficientSystem X b F) q)
      (isColimitPullbackCohomologyCocone X b c hc l hl F q) a
  refine ⟨i, aᵢ, ?_⟩
  rw [pullbackLimitCohomologyCocone_leg] at haᵢ
  exact haᵢ

include hc in
/-- A relation between actual stage classes that holds at the limit holds
after two actual transition morphisms to a common stage. -/
theorem exists_stage_cohomologyRelation (q : ℕ) (i j : I)
    (a : Sheaf.H.{e} ((inverseImage (b.π.app i).unop).obj F) q)
    (a' : Sheaf.H.{e} ((inverseImage (b.π.app j).unop).obj F) q)
    (h : ((pullbackLimitCohomologyCocone X b c l hl F q).ι.app i).hom a =
      ((pullbackLimitCohomologyCocone X b c l hl F q).ι.app j).hom a') :
    ∃ (t : I) (f : i ⟶ t) (g : j ⟶ t),
      ((diagramCohomologyFunctor X (pullbackCoefficientSystem X b F) q).map f).hom a =
        ((diagramCohomologyFunctor X (pullbackCoefficientSystem X b F) q).map g).hom a' := by
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{e}) :=
    preservesFilteredColimitsOfSize_of_univLE.{e, e, u, u} _
  let D : I ⥤ AddCommGrpCat.{e} :=
    diagramCohomologyFunctor X (pullbackCoefficientSystem X b F) q
  let C : Cocone D := pullbackLimitCohomologyCocone X b c l hl F q
  let hC : IsColimit C := isColimitPullbackCohomologyCocone X b c hc l hl F q
  exact concreteGroup_exists_relation D C hC a a' h

include hc in
/-- A stage class vanishing at the limit vanishes after an actual transition. -/
theorem exists_stage_cohomologyZero (q : ℕ) (i : I)
    (a : Sheaf.H.{e} ((inverseImage (b.π.app i).unop).obj F) q)
    (ha : ((pullbackLimitCohomologyCocone X b c l hl F q).ι.app i).hom a = 0) :
    ∃ (t : I) (f : i ⟶ t),
      ((diagramCohomologyFunctor X (pullbackCoefficientSystem X b F) q).map f).hom a = 0 := by
  have hi0 : ((pullbackLimitCohomologyCocone X b c l hl F q).ι.app i).hom 0 = 0 :=
    ((pullbackLimitCohomologyCocone X b c l hl F q).ι.app i).hom.map_zero
  obtain ⟨t, f, g, hfg⟩ := exists_stage_cohomologyRelation X b c hc l hl F q i i a 0
    (ha.trans hi0.symm)
  exact ⟨t, f, hfg.trans
    ((diagramCohomologyFunctor X (pullbackCoefficientSystem X b F) q).map g).hom.map_zero⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
