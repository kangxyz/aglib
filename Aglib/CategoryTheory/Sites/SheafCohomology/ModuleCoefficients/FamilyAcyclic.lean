/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.SectionLifting
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ProjectiveHomComplex
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyProjective

/-!
# Family Čech acyclicity and injective-cokernel stability

Only families of representables over a specified object are quantified. Their
original tuple presheaves are free on coproducts of representables of fiber
products. Arbitrary set-presheaf maps are deliberately not admitted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- Acyclicity of the original tuple Hom cochains for every representable
family over every object. -/
def FamilyCechAcyclic (F : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∀ (W : C) (ι : Type (max u v)) (U : ι → Over W) (n : ℕ),
    (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U) F.obj).ExactAt (n + 1)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

/-- The actual section-surjectivity supplied by local correction and gluing. -/
theorem FamilyCechAcyclic.sections_surjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FamilyCechAcyclic S.X₁) (W : C) :
    Function.Surjective (S.g.hom.app (op W)) :=
  sections_surjective_of_family_h1 J S hS (fun W ι U => hF W ι U 0) W

/-- Čech acyclicity of the kernel upgrades sheaf exactness to sectionwise
exactness for this original short exact sequence. -/
theorem FamilyCechAcyclic.presheaf_shortExact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FamilyCechAcyclic S.X₁) :
    (S.map (sheafToPresheaf J AddCommGrpCat)).ShortExact := by
  let : Mono S.f := hS.mono_f
  let (X : Cᵒᵖ) : Epi (S.g.hom.app X) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (FamilyCechAcyclic.sections_surjective S hS hF X.unop)
  exact {
    exact := hS.exact.map_of_mono_of_preservesKernel
      (sheafToPresheaf J AddCommGrpCat) inferInstance inferInstance
    mono_f := by
      change Mono ((sheafToPresheaf J AddCommGrpCat).map S.f)
      infer_instance
    epi_g := by
      change Epi S.g.hom
      exact NatTrans.epi_of_epi_app S.g.hom }

/-- The original free representable Hom map is surjective, with its degree-zero
normalization retained by the actual sections equivalence. -/
theorem FamilyCechAcyclic.hom_surjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FamilyCechAcyclic S.X₁) (W : C) :
    Function.Surjective (fun a : Hypercohomology.freeAbelianSheaf.{u} J W ⟶ S.X₂ =>
      a ≫ S.g) := by
  intro h
  obtain ⟨s, hs⟩ := FamilyCechAcyclic.sections_surjective S hS hF W
    (Hypercohomology.sectionsEquiv J W S.X₃ h)
  refine ⟨(Hypercohomology.sectionsEquiv J W S.X₂).symm s, ?_⟩
  apply (Hypercohomology.sectionsEquiv J W S.X₃).injective
  rw [Hypercohomology.sectionsEquiv_naturality, Equiv.apply_symm_apply, hs]

variable [∀ W : C, HasFiniteProducts (Over W)]

/-- Stability under quotients uses genuine sectionwise short exactness and
termwise projectivity of the original free tuple presheaves. -/
theorem FamilyCechAcyclic.quotient
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : FamilyCechAcyclic S.X₁) (hG : FamilyCechAcyclic S.X₂) :
    FamilyCechAcyclic S.X₃ := by
  intro W ι U n
  let K := Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U)
  let (i : ℕ) : Projective (K.X i) :=
    inferInstanceAs (Projective
      (Presheaf.Cech.tuplePresheaf (Presheaf.Cech.familyMap U) i ⋙ AddCommGrpCat.free))
  exact additiveHomFunctor_quotient_exactAt K (S.map (sheafToPresheaf J AddCommGrpCat))
    (FamilyCechAcyclic.presheaf_shortExact S hS hF) n (hF W ι U (n + 1)) (hG W ι U n)

end CategoryTheory.Sheaf.ModuleCoefficients
