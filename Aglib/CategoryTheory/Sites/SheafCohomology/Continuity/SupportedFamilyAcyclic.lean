/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FamilySectionLifting
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FamilyHomExact
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteFamilyAcyclic

/-! # Finite-family acyclicity on a specified class of site objects

Only the selected objects need finite supported covering refinements. The ambient
site can contain arbitrarily non-quasi-compact objects. The defining acyclicity
uses the original tuple cochains, not a cohomology-vanishing premise.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe e v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (P : C → Prop)

/-- Finite supported refinements are required only over supported target objects. -/
def HasFiniteSupportedRefinements : Prop :=
  ∀ (W : C), P W → ∀ (R : Sieve W), R ∈ J W →
    ∃ (ι : Type (max u v)) (_ : Finite ι) (U : ι → Over W),
      (∀ i, P (U i).left) ∧
      (Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W) ∧
      ∀ i, R (U i).hom

/-- Positive exactness of finite tuple cochains supported on the selected objects. -/
def SupportedFamilyCechAcyclic (F : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∀ (W : C), P W → ∀ (ι : Type (max u v)) [Finite ι] (U : ι → Over W),
    (∀ i, P (U i).left) → ∀ n : ℕ,
      (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U) F.obj).ExactAt (n + 1)

variable [HasSheafify J AddCommGrpCat.{max u v}]

/-- Original injective sheaves satisfy the supported-family condition. -/
theorem supportedFamilyCechAcyclic_of_injective
    (F : Sheaf J AddCommGrpCat.{max u v}) [Injective F] :
    SupportedFamilyCechAcyclic P F := by
  intro W _ ι _ U _ n
  exact finiteFamilyCechAcyclic_of_injective F W ι U n

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

/-- Supported degree-one exactness corrects local lifts over each supported object. -/
theorem SupportedFamilyCechAcyclic.sections_surjective
    (hcov : HasFiniteSupportedRefinements (J := J) P)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : SupportedFamilyCechAcyclic P S.X₁) (W : C) (hW : P W) :
    Function.Surjective (S.g.hom.app (op W)) := by
  intro s
  let : Epi S.g := hS.epi_g
  let : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr inferInstance
  obtain ⟨ι, hι, U, hU, hcover, hlift⟩ :=
    hcov W hW (Presheaf.imageSieve S.g.hom s) (Presheaf.imageSieve_mem J S.g.hom s)
  let : Finite ι := hι
  exact exists_section_lift_of_family_exact J S hS s U hcover hlift (hF W hW ι U hU 0)

variable [∀ W : C, HasFiniteProducts (Over W)]

/-- Finite tuple products remain among the supported objects. -/
def SupportedTupleProducts : Prop :=
  ∀ (W : C), P W → ∀ (ι : Type (max u v)) [Finite ι] (U : ι → Over W),
    (∀ i, P (U i).left) → ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      P (∏ᶜ fun i => U (a i)).left

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On supported tuples, local section lifting gives a genuine short exact
sequence of the original Hom cochain complexes. -/
theorem SupportedFamilyCechAcyclic.homComplex_shortExact
    (hcov : HasFiniteSupportedRefinements (J := J) P)
    (hprod : SupportedTupleProducts P)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : SupportedFamilyCechAcyclic P S.X₁)
    (W : C) (hW : P W) (ι : Type (max u v)) [Finite ι]
    (U : ι → Over W) (hU : ∀ i, P (U i).left) :
    (S.map (sheafToPresheaf J AddCommGrpCat ⋙
      additiveHomFunctor (Presheaf.Cech.freeComplex (Presheaf.Cech.familyMap U)))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  change (S.map (sheafToPresheaf J AddCommGrpCat ⋙ preadditiveCoyoneda.obj
    (op (Presheaf.Cech.tuplePresheaf (Presheaf.Cech.familyMap U) n ⋙
      AddCommGrpCat.free)))).ShortExact
  apply presheafHom_shortExact _ S hS
  intro f
  let V := fun a : Fin (n + 1) → ι => (∏ᶜ fun i => U (a i)).left
  let e : Presheaf.Cech.tuplePresheaf (Presheaf.Cech.familyMap U) n ⋙
      AddCommGrpCat.free ≅ Presheaf.Cech.familyPresheaf V ⋙ AddCommGrpCat.free :=
    Presheaf.Cech.freeFunctor.mapIso (Presheaf.Cech.tupleProductIso U n)
  obtain ⟨b, hb⟩ := freeFamilyHom_surjective V S.g
    (fun a => hF.sections_surjective P hcov S hS (V a) (hprod W hW ι U hU n a))
    (e.inv ≫ f)
  refine ⟨e.hom ≫ b, ?_⟩
  change b ≫ S.g.hom = e.inv ≫ f at hb
  change (e.hom ≫ b) ≫ S.g.hom = f
  rw [Category.assoc, hb, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Supported-family acyclicity is stable under an acyclic short-exact quotient. -/
theorem SupportedFamilyCechAcyclic.quotient
    (hcov : HasFiniteSupportedRefinements (J := J) P)
    (hprod : SupportedTupleProducts P)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hF : SupportedFamilyCechAcyclic P S.X₁) (hG : SupportedFamilyCechAcyclic P S.X₂) :
    SupportedFamilyCechAcyclic P S.X₃ := by
  intro W hW ι _ U hU n
  have hT := hF.homComplex_shortExact P hcov hprod S hS W hW ι U hU
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₃ (n + 1) (n + 2) rfl).isZero_X₂
    ((hG W hW ι U hU n).isZero_homology.eq_of_src _ _)
    ((hF W hW ι U hU (n + 1)).isZero_homology.eq_of_tgt _ _)

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]

/-- Local supported-family exactness implies vanishing of original global
cohomology when the original terminal object is supported. -/
theorem SupportedFamilyCechAcyclic.cohomology_eq_zero
    (hcov : HasFiniteSupportedRefinements (J := J) P)
    (hprod : SupportedTupleProducts P)
    {F : Sheaf J AddCommGrpCat.{max u v}} (hF : SupportedFamilyCechAcyclic P F)
    {W : C} (hW : P W) (hT : IsTerminal W) (n : ℕ)
    (x : Sheaf.H.{e} F (n + 1)) : x = 0 :=
  cohomology_eq_zero_of_cokernel_stable hT (SupportedFamilyCechAcyclic P)
    (fun S hS hI h₁ => by
      let : Injective S.X₂ := hI
      exact h₁.quotient P hcov hprod S hS
        (supportedFamilyCechAcyclic_of_injective P S.X₂))
    (fun S hS _ h₁ => h₁.sections_surjective P hcov S hS W hW)
    hF n x

end CategoryTheory.Sheaf.ModuleCoefficients
