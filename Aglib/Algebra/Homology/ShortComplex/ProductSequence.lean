/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Split signed product sequences

An ordered augmentation pair and a signed difference form an original short
complex. Either pair of opposite invertible components supplies an explicit
splitting. The actual product comparison transports the same sequence through
an additive finite-limit-preserving functor.

Extracted from `Quillen.Aglib.Algebra.Homology.ShortComplex.ProductSequence`
at Quillen revision `8273990b7977bd87edfe94cd2be91dec64de79aa`; the original
objects, ordered arrows, signs and public declaration names are unchanged.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B D E : C} (α : A ⟶ B) (β : A ⟶ D) (γ : B ⟶ E) (δ : D ⟶ E)
  (h : α ≫ γ = β ≫ δ)
/-- The original ordered restriction pair and signed difference form a short complex. -/
def productSequence : ShortComplex C :=
  ShortComplex.mk (prod.lift α β) (prod.fst ≫ γ - prod.snd ≫ δ) (by
    simp [Preadditive.comp_sub, ← Category.assoc, h])
/-- If the first augmentation and second difference components are invertible, the original
signed product sequence has an explicit splitting. -/
def productSequenceSplitting [IsIso α] [IsIso δ] : (productSequence α β γ δ h).Splitting where
  r := show B ⨯ D ⟶ A from prod.fst ≫ inv α
  s := show E ⟶ B ⨯ D from prod.lift 0 (-inv δ)
  f_r := by simp [productSequence, ← Category.assoc]
  s_g := by simp [productSequence, Preadditive.comp_sub, ← Category.assoc]
  id := by
    have he : inv α ≫ β = γ ≫ inv δ := by
      apply (cancel_epi α).mp
      simp only [← Category.assoc, h]
      simp
    dsimp only [productSequence]
    apply prod.hom_ext
    · simp [Preadditive.add_comp, Category.assoc]
    · simp only [
        Preadditive.add_comp, Category.assoc, prod.lift_snd, Category.id_comp,
        Preadditive.sub_comp, Preadditive.comp_neg, IsIso.hom_inv_id, Category.comp_id]
      rw [he]
      simp
/-- The same literal maps give a short exact sequence. -/
theorem productSequence_shortExact [IsIso α] [IsIso δ] :
    (productSequence α β γ δ h).ShortExact :=
  (productSequenceSplitting α β γ δ h).shortExact
end CategoryTheory.ShortComplex
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B D E : C} (α : A ⟶ B) (β : A ⟶ D) (γ : B ⟶ E) (δ : D ⟶ E)
  (h : α ≫ γ = β ≫ δ)
/-- The same signed sequence splits using the other augmentation and difference components. -/
def productSequenceRightSplitting [IsIso β] [IsIso γ] :
    (productSequence α β γ δ h).Splitting where
  r := show B ⨯ D ⟶ A from prod.snd ≫ inv β
  s := show E ⟶ B ⨯ D from prod.lift (inv γ) 0
  f_r := by simp [productSequence, ← Category.assoc]
  s_g := by simp [productSequence, Preadditive.comp_sub, ← Category.assoc]
  id := by
    have he : inv β ≫ α = δ ≫ inv γ := by
      apply (cancel_epi β).mp
      simp only [← Category.assoc, ← h]
      simp
    dsimp only [productSequence]
    apply prod.hom_ext
    · simp only [Preadditive.add_comp, Category.assoc, prod.lift_fst, Category.id_comp,
        Preadditive.sub_comp, IsIso.hom_inv_id, Category.comp_id]
      rw [he]
      simp
    · simp [Preadditive.add_comp, Category.assoc]
/-- The alternative invertible components give short exactness of the same literal maps. -/
theorem productSequence_shortExact_right [IsIso β] [IsIso γ] :
    (productSequence α β γ δ h).ShortExact :=
  (productSequenceRightSplitting α β γ δ h).shortExact
end CategoryTheory.ShortComplex
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F]
  {A B E G : C} (α : A ⟶ B) (β : A ⟶ E) (γ : B ⟶ G) (δ : E ⟶ G)
  (h : α ≫ γ = β ≫ δ)
/-- The original product comparison identifies mapped signed restriction sequences. -/
def productSequenceMapIso :
    (productSequence α β γ δ h).map F ≅
      productSequence (F.map α) (F.map β) (F.map γ) (F.map δ)
        (by simp only [← F.map_comp, h]) := by
  refine ShortComplex.isoMk (Iso.refl _) (asIso (prodComparison F B E)) (Iso.refl _) ?_ ?_
  · symm
    change F.map (prod.lift α β) ≫ prodComparison F B E = 𝟙 _ ≫ prod.lift _ _
    apply prod.hom_ext <;> simp [← F.map_comp]
  · symm
    change F.map (prod.fst ≫ γ - prod.snd ≫ δ) ≫ 𝟙 _ =
      prodComparison F B E ≫ (prod.fst ≫ F.map γ - prod.snd ≫ F.map δ)
    simp [Functor.map_sub, Preadditive.comp_sub]
/-- Exactness of the original mapped sequence follows from its two invertible components. -/
theorem productSequence_map_shortExact [IsIso (F.map α)] [IsIso (F.map δ)] :
    ((productSequence α β γ δ h).map F).ShortExact :=
  ShortComplex.shortExact_of_iso (productSequenceMapIso F α β γ δ h).symm
    (productSequence_shortExact _ _ _ _ _)
end CategoryTheory.ShortComplex
end
