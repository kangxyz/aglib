/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Zero

/-! # Original generator and zero-degree source transport

The actual constant adjunction and ordinary section representations identify
source transport on every Hom from the value of its actual original identity
generator. The same statement on original Ext zero follows from Ext.addEquiv₀.
No degree-zero or cohomology square is an input.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Adjunction

universe uC vC uD vD eC eD

section Hom

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  (L : C ⥤ D)
  {K : AddCommGrpCat.{vC} ⥤ D} {Γ : D ⥤ AddCommGrpCat.{vC}}
  [K.Additive] (constantAdj : K ⊣ Γ)
  {P : C} {S : C ⥤ AddCommGrpCat.{vC}}
  (α : L ⋙ Γ ≅ S) (β : preadditiveCoyoneda.obj (op P) ≅ S)
  (b : K.obj (AddCommGrpCat.of (ULift.{vC} ℤ)) ⟶ L.obj P)
  (hb : α.hom.app P (integerHomSectionsAddEquiv constantAdj (L.obj P) b) =
    β.hom.app P (𝟙 P))

include hb in
/-- The original identity-generator value determines every actual source Hom value. -/
theorem integerHomSections_source_of_generator {M : C} (a : P ⟶ M) :
    α.hom.app M (integerHomSectionsAddEquiv constantAdj (L.obj M) (b ≫ L.map a)) =
      β.hom.app M a := by
  have h₁ := integerHomSectionsAddEquiv_naturality constantAdj (L.map a) b
  have h₂ := ConcreteCategory.congr_hom (α.hom.naturality a)
    (integerHomSectionsAddEquiv constantAdj (L.obj P) b)
  have h₃ := ConcreteCategory.congr_hom (β.hom.naturality a) (𝟙 P)
  calc
    _ = α.hom.app M (Γ.map (L.map a)
        (integerHomSectionsAddEquiv constantAdj (L.obj P) b)) := congrArg (α.hom.app M) h₁
    _ = S.map a (α.hom.app P (integerHomSectionsAddEquiv constantAdj (L.obj P) b)) := h₂
    _ = S.map a (β.hom.app P (𝟙 P)) := congrArg (S.map a) hb
    _ = β.hom.app M ((𝟙 P) ≫ a) := h₃.symm
    _ = β.hom.app M a := congrArg (β.hom.app M) (Category.id_comp a)

end Hom

section Ext

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{eD} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {K : AddCommGrpCat.{vC} ⥤ D} {Γ : D ⥤ AddCommGrpCat.{vC}}
  [K.Additive] (constantAdj : K ⊣ Γ)
  {P : C} {S : C ⥤ AddCommGrpCat.{vC}}
  (α : L ⋙ Γ ≅ S) (β : preadditiveCoyoneda.obj (op P) ≅ S)
  (b : K.obj (AddCommGrpCat.of (ULift.{vC} ℤ)) ⟶ L.obj P)
  (hb : α.hom.app P (integerHomSectionsAddEquiv constantAdj (L.obj P) b) =
    β.hom.app P (𝟙 P))

include hb in
/-- Original Ext-zero source transport has exactly the same generator-normalized section value. -/
theorem integerExtZeroSections_source_of_generator {M : C} (x : Ext.{eC} P M 0) :
    α.hom.app M (integerExtZeroSectionsEquiv constantAdj (L.obj M)
        (L.extPrecompMap b M 0 x)) = β.hom.app M (Ext.addEquiv₀ x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ M).surjective x
  rw [Functor.extPrecompMap_mk₀, integerExtZeroSectionsEquiv_mk₀]
  have h : Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  rw [h]
  exact integerHomSections_source_of_generator L constantAdj α β b hb a

end Ext

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

universe uC vC uD vD eC eD

/-- A natural original Hom-section family and its actual source generator
normalize the complete original Ext-zero value. The comparison, evaluation
function and output value stay explicit through their defining equations. -/
theorem extZero_source_value_of_generator
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{eD} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {P : C} {Q : D} {S : C ⥤ AddCommGrpCat.{vC}}
    (E : ∀ M : C, (Q ⟶ L.obj M) → S.obj M)
    (hE : ∀ {M N : C} (q : M ⟶ N) (a : Q ⟶ L.obj M),
      E N (a ≫ L.map q) = S.map q (E M a))
    (β : preadditiveCoyoneda.obj (op P) ⟶ S) (b : Q ⟶ L.obj P)
    (hb : E P b = β.app P (𝟙 P))
    {M : C} (x : Ext.{eC} P M 0) (z : Ext.{eD} Q (L.obj M) 0)
    (hz : z = (Ext.mk₀ b).comp (x.mapExactFunctor L) (Nat.zero_add 0))
    (T : Ext.{eD} Q (L.obj M) 0 → S.obj M)
    (hT : T = fun y => E M (Ext.addEquiv₀ y)) (t : S.obj M)
    (ht : t = β.app M (Ext.addEquiv₀ x)) : T z = t := by
  rw [hT, ht, hz]
  change E M (Ext.addEquiv₀
    ((Ext.mk₀ b).comp (x.mapExactFunctor L) (Nat.zero_add 0))) =
      β.app M (Ext.addEquiv₀ x)
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective P M).surjective x
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  have ha : Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  have hb' : Ext.addEquiv₀ (Ext.mk₀ (b ≫ L.map a)) = b ≫ L.map a :=
    Ext.addEquiv₀.apply_symm_apply (b ≫ L.map a)
  rw [ha, hb']
  have hβ := ConcreteCategory.congr_hom (β.naturality a) (𝟙 P)
  calc
    E M (b ≫ L.map a) = S.map a (E P b) := hE a b
    _ = S.map a (β.app P (𝟙 P)) := congrArg (S.map a) hb
    _ = β.app M ((𝟙 P) ≫ a) := hβ.symm
    _ = β.app M a := congrArg (β.app M) (Category.id_comp a)

end CategoryTheory.Functor
