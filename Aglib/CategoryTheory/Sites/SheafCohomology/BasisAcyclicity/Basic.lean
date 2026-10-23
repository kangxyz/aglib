/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Quotient
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic

/-! # Original cohomology vanishing from cofinal basis Čech acyclicity

This is the dimension-shifting criterion of Stacks 03F9. Its class is defined by
Čech exactness, not by the cohomology vanishing that the theorem concludes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

open ModuleCoefficients

universe e c h w

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasSheafify J AddCommGrpCat.{max w h}]
  {B : CoverBasis.{c, h, w} J}

/-- Injectivity of abelian sheaves implies selected-cover Čech acyclicity,
using exact abelian sheafification, not scalar-forgetting. -/
theorem cechAcyclic_of_injective (F : Sheaf J AddCommGrpCat.{max w h}) [Injective F] :
    CechAcyclic B F := by
  let : (sheafToPresheaf J AddCommGrpCat.{max w h}).PreservesInjectiveObjects :=
    sheafToPresheaf_preservesInjectiveObjects J
  have : Injective F.obj :=
    inferInstanceAs (Injective ((sheafToPresheaf J AddCommGrpCat.{max w h}).obj F))
  intro W ι U _ n
  exact Presheaf.Cech.additiveHomComplex_exactAt_succ_of_injective
    (Presheaf.Cech.familyMap U) F.obj n

variable [J.WEqualsLocallyBijective (Type (max w h))]
  [J.PreservesSheafification AddCommGrpCat.free.{max w h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w h}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max w h})]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max w h})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max w h})]

/-- Positive original represented-object Ext vanishes on each basis object. -/
theorem CechAcyclic.ext_eq_zero {F : Sheaf J AddCommGrpCat.{max w h}}
    (hF : CechAcyclic B F) (W : C) (hW : B.objects W) (n : ℕ)
    (x : Ext.{e} (Hypercohomology.freeAbelianSheaf.{w} J W) F (n + 1)) : x = 0 := by
  apply Ext.eq_zero_of_cokernel_stable _ (CechAcyclic B)
    (fun S hS hI h₁ => by
      let : Injective S.X₂ := hI
      exact h₁.quotient S hS (cechAcyclic_of_injective S.X₂)) _ hF n x
  intro S hS _ h₁ a
  obtain ⟨s, hs⟩ := h₁.sections_surjective S hS W hW
    (Hypercohomology.sectionsEquiv J W S.X₃ a)
  refine ⟨(Hypercohomology.sectionsEquiv J W S.X₂).symm s, ?_⟩
  apply (Hypercohomology.sectionsEquiv J W S.X₃).injective
  rw [Hypercohomology.sectionsEquiv_naturality, Equiv.apply_symm_apply, hs]

/-- Positive original `Sheaf.H` vanishes when the terminal object lies on the
basis. This retains the original constant-integer source and arbitrary Ext size. -/
theorem CechAcyclic.cohomology_eq_zero {F : Sheaf J AddCommGrpCat.{max w h}}
    (hF : CechAcyclic B F) {T : C} (hT : IsTerminal T) (hBT : B.objects T)
    (n : ℕ) (x : Sheaf.H.{e} F (n + 1)) : x = 0 :=
  cohomology_eq_zero_of_cokernel_stable hT (CechAcyclic B)
    (fun S hS hI h₁ => by
      let : Injective S.X₂ := hI
      exact h₁.quotient S hS (cechAcyclic_of_injective S.X₂))
    (fun S hS _ h₁ => h₁.sections_surjective S hS T hBT) hF n x

end CategoryTheory.Sheaf.BasisAcyclicity
