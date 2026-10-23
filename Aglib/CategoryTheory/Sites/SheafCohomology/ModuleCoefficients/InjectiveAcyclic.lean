/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Acyclic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.PresheafInjective

/-!
# Original sheaf-cohomology acyclicity from section lifting

This file connects sectionwise lifting and cokernel stability to the original
native `Sheaf.H` groups, not to a replacement cohomology construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe e w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  {T : C} (hT : IsTerminal T)

/-- The original constant integer sheaf represents sections at a terminal object. -/
def constantHomSectionsEquiv (F : Sheaf J AddCommGrpCat.{w}) :
    ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) ≃
      F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat hT).homEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

omit [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] in
lemma constantHomSectionsEquiv_naturality {F G : Sheaf J AddCommGrpCat.{w}}
    (f : F ⟶ G)
    (a : (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    constantHomSectionsEquiv hT G (a ≫ f) =
      f.hom.app (op T) (constantHomSectionsEquiv hT F a) := rfl

/-- A genuine section-lifting class stable under injective cokernels has vanishing
positive original sheaf cohomology. -/
theorem cohomology_eq_zero_of_cokernel_stable (hT : IsTerminal T)
    (P : Sheaf J AddCommGrpCat.{w} → Prop)
    (hquot : ∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{w})),
      S.ShortExact → Injective S.X₂ → P S.X₁ → P S.X₃)
    (hsurj : ∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{w})),
      S.ShortExact → Injective S.X₂ → P S.X₁ →
        Function.Surjective (S.g.hom.app (op T)))
    {F : Sheaf J AddCommGrpCat.{w}} (hF : P F) (n : ℕ)
    (x : Sheaf.H F (n + 1)) : x = 0 := by
  apply Ext.eq_zero_of_cokernel_stable _ P hquot _ hF n x
  intro S hS hI hP a
  obtain ⟨s, hs⟩ := hsurj S hS hI hP (constantHomSectionsEquiv hT S.X₃ a)
  refine ⟨(constantHomSectionsEquiv hT S.X₂).symm s, ?_⟩
  apply (constantHomSectionsEquiv hT S.X₃).injective
  rw [constantHomSectionsEquiv_naturality, Equiv.apply_symm_apply]
  exact hs

end CategoryTheory.Sheaf.ModuleCoefficients

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe e e' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- Injective abelian sheaves satisfy the actual family tuple-cochain predicate. -/
theorem familyCechAcyclic_of_injective (F : Sheaf J AddCommGrpCat.{max u v})
    [Injective F] : FamilyCechAcyclic F := by
  let : (sheafToPresheaf J AddCommGrpCat.{max u v}).PreservesInjectiveObjects :=
    sheafToPresheaf_preservesInjectiveObjects J
  have : Injective F.obj :=
    inferInstanceAs (Injective ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj F))
  intro W ι U n
  exact Presheaf.Cech.additiveHomComplex_exactAt_succ_of_injective
    (Presheaf.Cech.familyMap U) F.obj n

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]

/-- Original represented-object Ext vanishes on the genuine family-acyclic class. -/
theorem FamilyCechAcyclic.ext_eq_zero {F : Sheaf J AddCommGrpCat.{max u v}}
    (hF : FamilyCechAcyclic F) (W : C) (n : ℕ)
    (x : Ext.{e} (Hypercohomology.freeAbelianSheaf.{u} J W) F (n + 1)) : x = 0 :=
  Ext.eq_zero_of_cokernel_stable _ FamilyCechAcyclic
    (fun S hS hI h₁ => by
      let : Injective S.X₂ := hI
      exact h₁.quotient S hS (familyCechAcyclic_of_injective S.X₂))
    (fun S hS _ h₁ => h₁.hom_surjective S hS W) hF n x

/-- Original global sheaf cohomology vanishes on the same class. -/
theorem FamilyCechAcyclic.cohomology_eq_zero
    {F : Sheaf J AddCommGrpCat.{max u v}} (hF : FamilyCechAcyclic F)
    {T : C} (hT : IsTerminal T) (n : ℕ) (x : Sheaf.H.{e} F (n + 1)) : x = 0 :=
  cohomology_eq_zero_of_cokernel_stable hT FamilyCechAcyclic
    (fun S hS hI h₁ => by
      let : Injective S.X₂ := hI
      exact h₁.quotient S hS (familyCechAcyclic_of_injective S.X₂))
    (fun S hS _ h₁ => h₁.sections_surjective S hS T) hF n x

omit [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)] in
/-- An injective original module sheaf is family-acyclic after forgetting scalars.
The original scalar ring is unchanged; it may live in the smaller hom universe. -/
theorem familyCechAcyclic_toSheaf_of_injective
    (R : Sheaf J RingCat.{v}) (I : SheafOfModules.{max u v} R) [Injective I] :
    FamilyCechAcyclic ((SheafOfModules.toSheaf R).obj I) := by
  have : Injective ((SheafOfModules.forget R).obj I) := inferInstance
  intro W ι U n
  exact PresheafOfModules.Cech.additiveHomComplex_exactAt_succ.{v, u, v, max u v}
    R.obj (Presheaf.Cech.familyMap U) ((SheafOfModules.forget R).obj I) n

/-- The original positive `Sheaf.H` groups of the underlying injective module vanish. -/
theorem toSheaf_injective_cohomology_subsingleton
    (R : Sheaf J RingCat.{v}) (I : SheafOfModules.{max u v} R) [Injective I]
    {T : C} (hT : IsTerminal T) (n : ℕ) :
    Subsingleton (Sheaf.H.{e} ((SheafOfModules.toSheaf R).obj I) (n + 1)) :=
  subsingleton_of_forall_eq 0 fun x =>
    (familyCechAcyclic_toSheaf_of_injective R I).cohomology_eq_zero hT n x

/-- The same vanishing retains the original free representable source at every object. -/
theorem toSheaf_injective_ext_subsingleton
    (R : Sheaf J RingCat.{v}) (I : SheafOfModules.{max u v} R) [Injective I]
    (W : C) (n : ℕ) :
    Subsingleton (Ext.{e} (Hypercohomology.freeAbelianSheaf.{u} J W)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) :=
  subsingleton_of_forall_eq 0 fun x =>
    (familyCechAcyclic_toSheaf_of_injective R I).ext_eq_zero W n x


omit [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)] in
/-- An injective original module sheaf is family-acyclic after forgetting scalars.
The original scalar ring and module values share the site-compatible larger universe. -/
theorem familyCechAcyclic_toSheaf_of_injective_largeScalars
    (R : Sheaf J RingCat.{max u v}) (I : SheafOfModules.{max u v} R) [Injective I] :
    FamilyCechAcyclic ((SheafOfModules.toSheaf R).obj I) := by
  have : Injective ((SheafOfModules.forget R).obj I) := inferInstance
  intro W ι U n
  exact PresheafOfModules.Cech.additiveHomComplex_exactAt_succ.{max u v, u, v, max u v}
    R.obj (Presheaf.Cech.familyMap U) ((SheafOfModules.forget R).obj I) n

/-- The same original positive cohomology vanishes for coefficients over a large scalar ring. -/
theorem toSheaf_injective_cohomology_subsingleton_largeScalars
    (R : Sheaf J RingCat.{max u v}) (I : SheafOfModules.{max u v} R) [Injective I]
    {T : C} (hT : IsTerminal T) (n : ℕ) :
    Subsingleton (Sheaf.H.{e} ((SheafOfModules.toSheaf R).obj I) (n + 1)) :=
  subsingleton_of_forall_eq 0 fun x =>
    (familyCechAcyclic_toSheaf_of_injective_largeScalars R I).cohomology_eq_zero hT n x

/-- The large-scalar variant retains the original free representable source at every object. -/
theorem toSheaf_injective_ext_subsingleton_largeScalars
    (R : Sheaf J RingCat.{max u v}) (I : SheafOfModules.{max u v} R) [Injective I]
    (W : C) (n : ℕ) :
    Subsingleton (Ext.{e} (Hypercohomology.freeAbelianSheaf.{u} J W)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) :=
  subsingleton_of_forall_eq 0 fun x =>
    (familyCechAcyclic_toSheaf_of_injective_largeScalars R I).ext_eq_zero W n x


end CategoryTheory.Sheaf.ModuleCoefficients
