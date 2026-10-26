/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedExt
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Abstract factories for actual module-valued derived comparisons

The original module source and the complete represented comparison are fixed
before specializing to a full subcategory of module sheaves. Both factories
are exactly the original additive-equivalence compositions, with no new objects.
-/

@[expose] public noncomputable section

universe u v w r s t z

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

section Represented

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] {B : Type r} [Ring B]

/-- Original module-valued comparison through an actual represented natural isomorphism. -/
abbrev representedDerivedModuleAddEquiv (P : C) (F : C ⥤ ModuleCat.{v} B) (n : ℕ)
    (β : F ⋙ forget₂ (ModuleCat.{v} B) AddCommGrpCat ≅
      (preadditiveCoyoneda.obj (op P)).rightDerived n) (M : C) :
    F.obj M ≃+ Ext.{w} P M n :=
  CategoryTheory.Abelian.representedDerivedModuleAddEquiv P F n β M

end Represented

section Scalar

variable {C : Type u} [Category.{v} C]
  {B : Type r} [Ring B] {Λ : Type s} [Ring Λ]

/-- Original scalar restriction comparison followed by a given additive identification. -/
def scalarDerivedModuleAddEquiv (F : C ⥤ ModuleCat.{t} B)
    (G : C ⥤ ModuleCat.{t} Λ) (α : Λ →+* B)
    (β : G ≅ F ⋙ ModuleCat.restrictScalars α) (M : C)
    {Z : Type z} [AddCommGroup Z] (e : F.obj M ≃+ Z) : G.obj M ≃+ Z :=
  (((forget₂ (ModuleCat.{t} Λ) AddCommGrpCat).mapIso
    (β.app M)).addCommGroupIsoToAddEquiv).trans e

end Scalar

end CategoryTheory.Sheaf.ModuleCoefficients
