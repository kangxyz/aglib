/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteSectionLifting
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ProjectiveHomComplex
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyProjective

/-! # Finite-family Čech acyclicity

Finite covering refinements let finite-family tuple-cochain acyclicity imply
actual section lifting and injective-cokernel stability. The final theorems
annihilate the original represented Ext groups and `Sheaf.H`, with an explicit
independent Ext universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe e v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- Acyclicity of the original tuple Hom cochains for finite representable
families over every object. -/
def FiniteFamilyCechAcyclic (F : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∀ (W : C) (ι : Type (max u v)) [Finite ι] (U : ι → Over W) (n : ℕ),
    (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U) F.obj).ExactAt (n + 1)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

variable (H : J.OneHypercoverFamily.{max u v}) [H.IsGenerating]
  (hfin : ∀ ⦃X : C⦄ (E : J.OneHypercover.{max u v} X), H E → Finite E.I₀)

include H hfin in
/-- The actual section-surjectivity supplied by local correction and gluing. -/
theorem FiniteFamilyCechAcyclic.sections_surjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FiniteFamilyCechAcyclic S.X₁) (W : C) :
    Function.Surjective (S.g.hom.app (op W)) :=
  sections_surjective_of_finite_family_h1 J H hfin S hS
    (fun W ι _ U => hF W ι U 0) W

include H hfin in
/-- Čech acyclicity of the kernel upgrades sheaf exactness to sectionwise
exactness for this original short exact sequence. -/
theorem FiniteFamilyCechAcyclic.presheaf_shortExact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FiniteFamilyCechAcyclic S.X₁) :
    (S.map (sheafToPresheaf J AddCommGrpCat)).ShortExact := by
  let : Mono S.f := hS.mono_f
  let (X : Cᵒᵖ) : Epi (S.g.hom.app X) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (FiniteFamilyCechAcyclic.sections_surjective H hfin S hS hF X.unop)
  exact {
    exact := hS.exact.map_of_mono_of_preservesKernel
      (sheafToPresheaf J AddCommGrpCat) inferInstance inferInstance
    mono_f := by
      change Mono ((sheafToPresheaf J AddCommGrpCat).map S.f)
      infer_instance
    epi_g := by
      change Epi S.g.hom
      exact NatTrans.epi_of_epi_app S.g.hom }

include H hfin in
/-- The original free representable Hom map is surjective, with its degree-zero
normalization retained by the actual sections equivalence. -/
theorem FiniteFamilyCechAcyclic.hom_surjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FiniteFamilyCechAcyclic S.X₁) (W : C) :
    Function.Surjective (fun a : Hypercohomology.freeAbelianSheaf.{u} J W ⟶ S.X₂ =>
      a ≫ S.g) := by
  intro h
  obtain ⟨s, hs⟩ := FiniteFamilyCechAcyclic.sections_surjective H hfin S hS hF W
    (Hypercohomology.sectionsEquiv J W S.X₃ h)
  refine ⟨(Hypercohomology.sectionsEquiv J W S.X₂).symm s, ?_⟩
  apply (Hypercohomology.sectionsEquiv J W S.X₃).injective
  rw [Hypercohomology.sectionsEquiv_naturality, Equiv.apply_symm_apply, hs]

variable [∀ W : C, HasFiniteProducts (Over W)]

include H hfin in
/-- Stability under quotients uses genuine sectionwise short exactness and
termwise projectivity of the original free tuple presheaves. -/
theorem FiniteFamilyCechAcyclic.quotient
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FiniteFamilyCechAcyclic S.X₁) (hG : FiniteFamilyCechAcyclic S.X₂) :
    FiniteFamilyCechAcyclic S.X₃ := by
  intro W ι _ U n
  let K := Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U)
  let (i : ℕ) : Projective (K.X i) :=
    inferInstanceAs (Projective
      (Presheaf.Cech.tuplePresheaf (Presheaf.Cech.familyMap U) i ⋙ AddCommGrpCat.free))
  exact additiveHomFunctor_quotient_exactAt K (S.map (sheafToPresheaf J AddCommGrpCat))
    (FiniteFamilyCechAcyclic.presheaf_shortExact H hfin S hS hF) n (hF W ι U (n + 1)) (hG W ι U n)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)] in
/-- Injective sheaves satisfy finite-family acyclicity through the existing
actual tuple-cochain injective theorem. -/
theorem finiteFamilyCechAcyclic_of_injective
    (F : Sheaf J AddCommGrpCat.{max u v}) [Injective F] :
    FiniteFamilyCechAcyclic F := by
  intro W ι _ U n
  exact familyCechAcyclic_of_injective F W ι U n

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]

include H hfin in
/-- Finite-family acyclicity annihilates the original represented-object Ext. -/
theorem FiniteFamilyCechAcyclic.ext_eq_zero
    {F : Sheaf J AddCommGrpCat.{max u v}} (hF : FiniteFamilyCechAcyclic F)
    (W : C) (n : ℕ)
    (x : Ext.{e} (Hypercohomology.freeAbelianSheaf.{u} J W) F (n + 1)) : x = 0 :=
  Ext.eq_zero_of_cokernel_stable _ FiniteFamilyCechAcyclic
    (fun S hS hI h₁ => by
      let : Injective S.X₂ := hI
      exact FiniteFamilyCechAcyclic.quotient H hfin S hS h₁
        (finiteFamilyCechAcyclic_of_injective S.X₂))
    (fun S hS _ h₁ => FiniteFamilyCechAcyclic.hom_surjective H hfin S hS h₁ W)
    hF n x

include H hfin in
/-- The same dimension shift annihilates positive original global cohomology. -/
theorem FiniteFamilyCechAcyclic.cohomology_eq_zero
    {F : Sheaf J AddCommGrpCat.{max u v}} (hF : FiniteFamilyCechAcyclic F)
    {T : C} (hT : IsTerminal T) (n : ℕ) (x : Sheaf.H.{e} F (n + 1)) : x = 0 :=
  cohomology_eq_zero_of_cokernel_stable hT FiniteFamilyCechAcyclic
    (fun S hS hI h₁ => by
      let : Injective S.X₂ := hI
      exact FiniteFamilyCechAcyclic.quotient H hfin S hS h₁
        (finiteFamilyCechAcyclic_of_injective S.X₂))
    (fun S hS _ h₁ => FiniteFamilyCechAcyclic.sections_surjective H hfin S hS h₁ T)
    hF n x

end CategoryTheory.Sheaf.ModuleCoefficients
