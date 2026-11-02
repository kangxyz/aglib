/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Pullback
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison

/-! # Original degree-zero integer cohomology and sections

The native Ext-to-Hom equivalence followed by the actual constant adjunction
and original integer-one evaluation gives ordinary sections. Its original
source pullback is exactly the actual unit-section map, including the inverse
equation. No derived-category realization or injective source is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

universe uC vC uD vD s eC eD

section Zero

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  [K.Additive] (constantAdj : K ⊣ Γ)

/-- The original Ext-zero comparison, actual constant adjunction and integer one. -/
def integerExtZeroSectionsEquiv (Y : C) :
    Ext.{eC} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y 0 ≃+ Γ.obj Y :=
  Ext.addEquiv₀.trans (integerHomSectionsAddEquiv constantAdj Y)

/-- The comparison evaluates the original degree-zero morphism. -/
theorem integerExtZeroSectionsEquiv_mk₀ {Y : C}
    (a : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ Y) :
    integerExtZeroSectionsEquiv constantAdj Y (Ext.mk₀ a) =
      integerHomSectionsAddEquiv constantAdj Y a := by
  change integerHomSectionsAddEquiv constantAdj Y (Ext.addEquiv₀ (Ext.mk₀ a)) = _
  have ha : Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  exact congrArg (integerHomSectionsAddEquiv constantAdj Y) ha

/-- Original coefficient postcomposition is the actual map on zero-degree sections. -/
theorem integerExtZeroSectionsEquiv_coefficient {Y Z : C} (q : Y ⟶ Z)
    (x : Ext.{eC} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y 0) :
    integerExtZeroSectionsEquiv constantAdj Z (x.comp (Ext.mk₀ q) (add_zero 0)) =
      Γ.map q (integerExtZeroSectionsEquiv constantAdj Y x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ Y).surjective x
  rw [Ext.mk₀_comp_mk₀, integerExtZeroSectionsEquiv_mk₀, integerExtZeroSectionsEquiv_mk₀]
  exact integerHomSectionsAddEquiv_naturality constantAdj q a

end Zero

section Pullback

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{eD} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  {K' : AddCommGrpCat.{s} ⥤ D} {Δ : D ⥤ AddCommGrpCat.{s}}
  [K.Additive] [K'.Additive]
  (constantAdj : K ⊣ Γ) (imageAdj : F ⊣ G) (constantAdj' : K' ⊣ Δ)
  (e : G ⋙ Γ ≅ Δ) (c : K ⋙ F ≅ K')
  (hc : c = leftAdjointCompIso constantAdj imageAdj constantAdj' e)

include hc in
/-- Degree-zero original source pullback is the actual ordinary unit-section map. -/
theorem integerExtZeroSectionsEquiv_pullback (Y : C)
    (x : Ext.{eC} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y 0) :
    integerExtZeroSectionsEquiv constantAdj' (F.obj Y)
        (F.extPrecompMap (c.inv.app (AddCommGrpCat.of (ULift.{s} ℤ))) Y 0 x) =
      (unitSectionsNatTrans imageAdj Γ e).app Y
        (integerExtZeroSectionsEquiv constantAdj Y x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ Y).surjective x
  rw [Functor.extPrecompMap_mk₀, integerExtZeroSectionsEquiv_mk₀,
    integerExtZeroSectionsEquiv_mk₀]
  exact integerHomSectionsAddEquiv_pullback constantAdj imageAdj constantAdj' e c hc a

include hc in
/-- The same original normalization in the direction from actual sections. -/
theorem integerExtZeroSectionsEquiv_pullback_symm (Y : C) (z : Γ.obj Y) :
    F.extPrecompMap (c.inv.app (AddCommGrpCat.of (ULift.{s} ℤ))) Y 0
        ((integerExtZeroSectionsEquiv constantAdj Y).symm z) =
      (integerExtZeroSectionsEquiv constantAdj' (F.obj Y)).symm
        ((unitSectionsNatTrans imageAdj Γ e).app Y z) := by
  apply (integerExtZeroSectionsEquiv constantAdj' (F.obj Y)).injective
  rw [integerExtZeroSectionsEquiv_pullback constantAdj imageAdj constantAdj' e c hc,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

include hc in
/-- Complete original zero-degree transfer is section pullback followed by
the actual coefficient map. -/
theorem integerExtZeroSectionsEquiv_transfer {Y : C} {Z : D} (φ : F.obj Y ⟶ Z)
    (x : Ext.{eC} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y 0) :
    integerExtZeroSectionsEquiv constantAdj' Z
        ((F.extPrecompMap (c.inv.app (AddCommGrpCat.of (ULift.{s} ℤ))) Y 0 x).comp
          (Ext.mk₀ φ) (add_zero 0)) =
      Δ.map φ ((unitSectionsNatTrans imageAdj Γ e).app Y
        (integerExtZeroSectionsEquiv constantAdj Y x)) := by
  rw [integerExtZeroSectionsEquiv_coefficient,
    integerExtZeroSectionsEquiv_pullback constantAdj imageAdj constantAdj' e c hc]

end Pullback

end CategoryTheory.Adjunction
