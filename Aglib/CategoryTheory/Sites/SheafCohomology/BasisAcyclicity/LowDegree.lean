/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CoverAugmentation
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.AugmentationExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The degree-two Čech class-and-primitive criterion

Two actual kernel short exact sequences represent a degree-two Ext class killed
by an augmented cover. Vanishing of Ext¹ on the degree-one term produces a
literal degree-two cocycle. A primitive for that cocycle kills the original Ext
class. No projectivity of the Čech terms, spectral sequence, or all-degree
acyclicity of overlaps is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.ModuleCoefficients

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h e

variable {C : Type c} [Category.{h} C] [Abelian C] [HasExt.{e} C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A class killed by the augmentation has a literal degree-two cocycle whose
primitives kill that original class. Only degree-one Ext of `K.X 1` is used. -/
theorem exists_degreeTwo_cocycle_of_augmentation
    {K : ChainComplex C ℕ} {Z A : C}
    (π : K ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso π]
    (h₁ : ∀ β : Ext (K.X 1) A 1, β = 0)
    (α : Ext Z A 2)
    (hα : (Ext.mk₀ (π.f 0)).comp α (Nat.zero_add 2) = 0) :
    ∃ c : K.X 2 ⟶ A, K.d 3 2 ≫ c = 0 ∧
      ((∃ t : K.X 1 ⟶ A, K.d 2 1 ≫ t = c) → α = 0) := by
  let g := π.f 0
  let q₁ : K.X 1 ⟶ kernel g := kernel.lift g (K.d 1 0) (augmentation_d_comp π)
  let S₀ := ShortComplex.kernelSequence g
  have hg : Epi g := augmentation_epi π
  let : Epi g := hg
  have hS₀ : S₀.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact g
      epi_g := by change Epi g; infer_instance }
  have hq₁ : Epi q₁ := (augmentation_exact π).epi_kernelLift
  let : Epi q₁ := hq₁
  let S₁ := ShortComplex.kernelSequence q₁
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact q₁
      epi_g := by change Epi q₁; infer_instance }
  have hd₂ : K.d 2 1 ≫ q₁ = 0 := by
    apply (cancel_mono (kernel.ι g)).mp
    simp only [Category.assoc, q₁, kernel.lift_ι, zero_comp, K.d_comp_d]
  let T := ShortComplex.mk (K.d 2 1) q₁ hd₂
  let φ : T ⟶ K.sc' 2 1 0 :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι g
      comm₁₂ := by
        change 𝟙 _ ≫ K.d 2 1 = K.d 2 1 ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        change 𝟙 _ ≫ K.d 1 0 = q₁ ≫ kernel.ι g
        simp only [Category.id_comp, q₁, kernel.lift_ι] }
  have : Epi φ.τ₁ := by change Epi (𝟙 (K.X 2)); infer_instance
  have : IsIso φ.τ₂ := by change IsIso (𝟙 (K.X 1)); infer_instance
  have : Mono φ.τ₃ := by change Mono (kernel.ι g); infer_instance
  have hK₁ : K.ExactAt 1 :=
    (exactAt_iff_of_quasiIsoAt π 1).2
      (ChainComplex.exactAt_succ_single_obj Z 0)
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    ((K.exactAt_iff' 2 1 0 (by simp) (by simp)).mp hK₁)
  let q₂ : K.X 2 ⟶ kernel q₁ := kernel.lift q₁ (K.d 2 1) hd₂
  let : Epi q₂ := hT.epi_kernelLift
  obtain ⟨β, hβ⟩ := Ext.contravariant_sequence_exact₃ hS₀ A α hα (n₀ := 1) rfl
  obtain ⟨γ, hγ⟩ := Ext.contravariant_sequence_exact₃ hS₁ A β
    (h₁ ((Ext.mk₀ S₁.g).comp β (Nat.zero_add 1))) (n₀ := 0) rfl
  let a : S₁.X₁ ⟶ A := Ext.homEquiv₀ γ
  have ha : hS₁.extClass.comp (Ext.mk₀ a) (by decide) = β := by
    simpa only [a, Ext.mk₀_homEquiv₀_apply] using hγ
  refine ⟨q₂ ≫ a, ?_, ?_⟩
  · have hz : K.d 3 2 ≫ q₂ = 0 := by
      apply (cancel_mono (kernel.ι q₁)).mp
      simp only [Category.assoc, q₂, kernel.lift_ι, zero_comp, K.d_comp_d]
    rw [← Category.assoc, hz, zero_comp]
  · rintro ⟨t, ht⟩
    have hat : kernel.ι q₁ ≫ t = a := by
      apply (cancel_epi q₂).mp
      simpa only [← Category.assoc, q₂, kernel.lift_ι] using ht
    have hβzero : β = 0 := by
      have hat' : S₁.f ≫ t = a := hat
      have hz : hS₁.extClass.comp (Ext.mk₀ (S₁.f ≫ t)) (Nat.add_zero 1) = 0 := by
        simpa only [Ext.mk₀_comp_mk₀] using hS₁.extClass_comp_assoc (Ext.mk₀ t)
      rw [hat', ha] at hz
      exact hz
    rw [hβzero, Ext.comp_zero] at hβ
    exact hβ.symm

/-- Exactness of the literal degree-two cochains kills every original degree-two
class whose pullback along the actual augmentation is zero. -/
theorem ext_two_eq_zero_of_augmentation_primitives
    {K : ChainComplex C ℕ} {Z A : C}
    (π : K ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso π]
    (h₁ : ∀ β : Ext (K.X 1) A 1, β = 0)
    (hprim : ∀ c : K.X 2 ⟶ A, K.d 3 2 ≫ c = 0 →
      ∃ t : K.X 1 ⟶ A, K.d 2 1 ≫ t = c)
    (α : Ext Z A 2)
    (hα : (Ext.mk₀ (π.f 0)).comp α (Nat.zero_add 2) = 0) : α = 0 := by
  obtain ⟨c, hc, hkill⟩ := exists_degreeTwo_cocycle_of_augmentation π h₁ α hα
  exact hkill (hprim c hc)

section Cech

universe s v r

open Opposite

variable {D : Type s} [Category.{v} D] {J : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective (Type r)]
  [J.PreservesSheafification AddCommGrpCat.free.{r}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{r})]
  {F G : Dᵒᵖ ⥤ Type r} (f : F ⟶ G) [Presheaf.IsLocallySurjective J f]

/-- The class-and-primitive criterion on the original sheafified free Čech
complex, with an independent value and Ext universe. -/
theorem exists_degreeTwo_cech_cocycle
    (A : Sheaf J AddCommGrpCat.{r})
    (h₁ : ∀ β : Ext ((Presheaf.Cech.sheafComplex f J).X 1) A 1, β = 0)
    (α : Ext ((presheafToSheaf J AddCommGrpCat).obj (G ⋙ AddCommGrpCat.free)) A 2)
    (hα : (Ext.mk₀ ((Presheaf.Cech.sheafAugmentation f J).f 0)).comp α
      (Nat.zero_add 2) = 0) :
    ∃ c : (Presheaf.Cech.sheafComplex f J).X 2 ⟶ A,
      (Presheaf.Cech.sheafComplex f J).d 3 2 ≫ c = 0 ∧
      ((∃ t : (Presheaf.Cech.sheafComplex f J).X 1 ⟶ A,
        (Presheaf.Cech.sheafComplex f J).d 2 1 ≫ t = c) → α = 0) := by
  let : QuasiIso (Presheaf.Cech.sheafAugmentation f J) :=
    Presheaf.Cech.sheafAugmentation_quasiIso_of_sizes f J
  exact exists_degreeTwo_cocycle_of_augmentation
    (Presheaf.Cech.sheafAugmentation f J) h₁ α hα

end Cech

end CategoryTheory.Sheaf.BasisAcyclicity
