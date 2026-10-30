/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.FiniteSumDescent
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal

/-! # Free-representable transfers from finite labelled local arrows

Only the label set on each chart is finite. The covering family is arbitrary,
and matching is imposed on the original represented sums on actual overlaps.
The resulting arrow retains every local sum and its terminal augmentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

universe c h t k l

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}] {T U : C} (hT : IsTerminal T)

/-- Glue the actual finite sums, form their free-source arrow, and prove its
local restrictions and its original terminal rank equation. -/
theorem exists_freeRepresentable_transfer_of_cover
    {K : Type k} (V : K → C) (p : ∀ i, V i ⟶ T)
    (hp : Sieve.ofArrows V p ∈ J T)
    (Label : K → Type l) [∀ i, Fintype (Label i)]
    (f : ∀ i, Label i → (V i ⟶ U))
    (matching : ∀ i j (W : C) (g : W ⟶ V i) (q : W ⟶ V j),
      g ≫ p i = q ≫ p j →
        (freeAbelianSheaf.{t} J U).obj.map g.op (representedSum J (f i)) =
          (freeAbelianSheaf.{t} J U).obj.map q.op (representedSum J (f j)))
    (n : ℕ) (hn : ∀ i, Fintype.card (Label i) = n) :
    ∃ τ : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U,
      (∀ i, (freeAbelianSheafFunctor.{t} J).map (p i) ≫ τ =
        ∑ a : Label i, (freeAbelianSheafFunctor.{t} J).map (f i a)) ∧
      τ ≫ (freeAbelianSheafFunctor.{t} J).map (hT.from U) = n • 𝟙 _ := by
  classical
  let F := freeAbelianSheaf.{t} J U
  obtain ⟨s, hs, _⟩ := existsUnique_section_of_cover J F V p hp
    (fun i => representedSum J (f i)) matching
  let τ := (sectionsAddEquiv.{t} J T F).symm s
  have hτ : sectionsAddEquiv.{t} J T F τ = s :=
    (sectionsAddEquiv.{t} J T F).apply_symm_apply s
  have hlocal (i : K) : (freeAbelianSheafFunctor.{t} J).map (p i) ≫ τ =
      ∑ a : Label i, (freeAbelianSheafFunctor.{t} J).map (f i a) := by
    apply (sectionsAddEquiv.{t} J (V i) F).injective
    calc
      _ = F.obj.map (p i).op (sectionsAddEquiv.{t} J T F τ) :=
        BasisAcyclicity.sectionsEquiv_precomp J (p i) F τ
      _ = representedSum J (f i) := (congrArg (F.obj.map (p i).op) hτ).trans (hs i)
      _ = _ := by
        simp only [map_sum, representedSum, representedGenerator]
        rfl
  refine ⟨τ, hlocal, ?_⟩
  apply (sectionsAddEquiv.{t} J T (freeAbelianSheaf.{t} J T)).injective
  apply section_eq_of_cover J V p hp
  intro i
  change (freeAbelianSheaf.{t} J T).obj.map (p i).op
      (sectionsEquiv.{t} J T _ _) =
    (freeAbelianSheaf.{t} J T).obj.map (p i).op (sectionsEquiv.{t} J T _ _)
  rw [← BasisAcyclicity.sectionsEquiv_precomp, ← BasisAcyclicity.sectionsEquiv_precomp]
  apply congrArg (sectionsEquiv.{t} J (V i) _)
  rw [← Category.assoc, hlocal, Preadditive.sum_comp]
  have heq (a : Label i) : f i a ≫ hT.from U = p i := hT.hom_ext _ _
  change (∑ a : Label i, (freeAbelianSheafFunctor.{t} J).map (f i a) ≫
      (freeAbelianSheafFunctor.{t} J).map (hT.from U)) =
    (freeAbelianSheafFunctor.{t} J).map (p i) ≫
      (n • 𝟙 ((freeAbelianSheafFunctor.{t} J).obj T))
  rw [Preadditive.comp_nsmul, Category.comp_id]
  calc
    _ = ∑ _a : Label i, (freeAbelianSheafFunctor.{t} J).map (p i) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact ((freeAbelianSheafFunctor.{t} J).map_comp _ _).symm.trans
        (congrArg (freeAbelianSheafFunctor.{t} J).map (heq a))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, hn i]

/-- Normalize the same free-source transfer with the original constant integer
source and the original free-terminal comparison. -/
theorem normalized_transfer_of_freeRepresentable
    (τ : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U) (n : ℕ)
    (hτ : τ ≫ (freeAbelianSheafFunctor.{t} J).map (hT.from U) = n • 𝟙 _) :
    ((constantIntegerFreeTerminalIso.{c, h, t} J hT).hom ≫ τ) ≫
      ((freeAbelianSheafFunctor.{t} J).map (hT.from U) ≫
        (constantIntegerFreeTerminalIso.{c, h, t} J hT).inv) = n • 𝟙 _ := by
  let e := constantIntegerFreeTerminalIso.{c, h, t} J hT
  change (e.hom ≫ τ) ≫ (_ ≫ e.inv) = n • 𝟙 _
  rw [Category.assoc, ← Category.assoc τ, hτ, Preadditive.nsmul_comp,
    Category.id_comp, Preadditive.comp_nsmul, Iso.hom_inv_id]

/-- Existence of a free transfer gives existence with exactly the native
constant-integer source, without changing either augmentation or rank. -/
theorem exists_normalized_transfer_of_freeRepresentable (n : ℕ)
    (h : ∃ τ : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U,
      τ ≫ (freeAbelianSheafFunctor.{t} J).map (hT.from U) = n • 𝟙 _) :
    ∃ τ : (constantSheaf J AddCommGrpCat.{max h t}).obj
        (AddCommGrpCat.of (ULift.{max h t} ℤ)) ⟶ freeAbelianSheaf.{t} J U,
      τ ≫ ((freeAbelianSheafFunctor.{t} J).map (hT.from U) ≫
        (constantIntegerFreeTerminalIso.{c, h, t} J hT).inv) = n • 𝟙 _ := by
  obtain ⟨τ, hτ⟩ := h
  exact ⟨(constantIntegerFreeTerminalIso.{c, h, t} J hT).hom ≫ τ,
    normalized_transfer_of_freeRepresentable J hT τ n hτ⟩

end CategoryTheory.Sheaf.Hypercohomology
