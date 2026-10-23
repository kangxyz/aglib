/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedScalarSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedExtNaturality

/-!
# Abstract coefficient naturality for represented derived sections

The complete functors, their isomorphism, and the normalization are abstract
before specializing to module sheaves. Original coefficient maps are retained.
-/

@[expose] public noncomputable section

universe u v w t r s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] (P : C)

/-- Original Ext naturality after an abstract natural represented normalization. -/
lemma representedIso_ext_naturality {B : Type r} [Ring B]
    (F : C ⥤ ModuleCat.{v} B) (n : ℕ)
    (β : F ⋙ forget₂ (ModuleCat.{v} B) AddCommGrpCat ≅
      (preadditiveCoyoneda.obj (op P)).rightDerived n)
    {M N : C} (f : M ⟶ N) (x : F.obj M) :
    representedDerivedModuleAddEquiv P F n β N (F.map f x) =
      (representedDerivedModuleAddEquiv P F n β M x).comp (Ext.mk₀ f) (add_zero n) := by
  apply (extRightDerivedRepresentedAddEquiv P N n).injective
  rw [extRightDerivedRepresentedAddEquiv_naturality]
  simp only [representedDerivedModuleAddEquiv, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (β.hom.naturality f) x

omit [EnoughInjectives C] in
/-- An arbitrary additive Ext normalization remains natural under scalar restriction. -/
lemma scalarIso_ext_naturality {B : Type r} [Ring B] {Λ : Type s} [Ring Λ]
    (F : C ⥤ ModuleCat.{t} B) (G : C ⥤ ModuleCat.{t} Λ) (α : Λ →+* B)
    (β : G ≅ F ⋙ ModuleCat.restrictScalars α) (n : ℕ)
    (E : ∀ M, F.obj M ≃+ Ext.{w} P M n)
    (hE : ∀ {M N : C} (f : M ⟶ N) (x : F.obj M),
      E N (F.map f x) = (E M x).comp (Ext.mk₀ f) (add_zero n))
    {M N : C} (f : M ⟶ N) (x : G.obj M) :
    scalarDerivedModuleAddEquiv F G α β N (E N) (G.map f x) =
      (scalarDerivedModuleAddEquiv F G α β M (E M) x).comp (Ext.mk₀ f) (add_zero n) := by
  have h := ConcreteCategory.congr_hom (β.hom.naturality f) x
  change β.hom.app N (G.map f x) = F.map f (β.hom.app M x) at h
  exact (congrArg (E N) h).trans (hE f (β.hom.app M x))

end CategoryTheory.Sheaf.ModuleCoefficients
