/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Exact rows for the original unsigned triangulated Yoneda boundary

The native contravariant Yoneda homology sequence gives exact rows with the original
triangle precomposition maps and `ShiftedHom.comp` by its actual connecting arrow.
Vanishing of the displayed middle next-degree Hom group makes that same boundary
surjective. The native boundary is unsigned; no alternative boundary map is defined.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

universe u v

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Original triangle precomposition and its actual unsigned boundary form an exact row. -/
theorem yoneda_exact_precomp_boundary (T : Triangle C) (hT : T ∈ distTriang C)
    (V : C) (i j : ℤ) (hij : i + 1 = j) :
    Function.Exact (fun f : T.obj₂ ⟶ V⟦i⟧ => T.mor₁ ≫ f)
      (fun f : T.obj₁ ⟶ V⟦i⟧ => ShiftedHom.comp T.mor₃ f hij) := by
  have h := (preadditiveYoneda.obj V).homologySequence_exact₃ _
    (op_distinguished T hT) i j hij
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  change Function.Exact (fun f : T.obj₂ ⟶ V⟦i⟧ => T.mor₁ ≫ f)
    (fun f : T.obj₁ ⟶ V⟦i⟧ => (preadditiveYoneda.obj V).homologySequenceδ
      ((triangleOpEquivalence C).functor.obj (op T)) i j hij f) at h
  simp only [preadditiveYoneda_homologySequenceδ_apply] at h
  simpa only [Functor.shift, ShiftedHom.comp] using! h

/-- The actual unsigned boundary and the next original precomposition form an exact row. -/
theorem yoneda_exact_boundary_precomp (T : Triangle C) (hT : T ∈ distTriang C)
    (V : C) (i j : ℤ) (hij : i + 1 = j) :
    Function.Exact (fun f : T.obj₁ ⟶ V⟦i⟧ => ShiftedHom.comp T.mor₃ f hij)
      (fun f : T.obj₃ ⟶ V⟦j⟧ => T.mor₂ ≫ f) := by
  have h := (preadditiveYoneda.obj V).homologySequence_exact₁ _
    (op_distinguished T hT) i j hij
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  change Function.Exact
    (fun f : T.obj₁ ⟶ V⟦i⟧ => (preadditiveYoneda.obj V).homologySequenceδ
      ((triangleOpEquivalence C).functor.obj (op T)) i j hij f)
    (fun f : T.obj₃ ⟶ V⟦j⟧ => T.mor₂ ≫ f) at h
  simp only [preadditiveYoneda_homologySequenceδ_apply] at h
  simpa only [Functor.shift, ShiftedHom.comp] using! h

/-- The same actual boundary is surjective when its next middle Hom group vanishes. -/
theorem yoneda_boundary_surjective_of_subsingleton (T : Triangle C)
    (hT : T ∈ distTriang C) (V : C) (i j : ℤ) (hij : i + 1 = j)
    [Subsingleton (T.obj₂ ⟶ V⟦j⟧)] :
    Function.Surjective (fun f : T.obj₁ ⟶ V⟦i⟧ => ShiftedHom.comp T.mor₃ f hij) := by
  intro f
  exact (yoneda_exact_boundary_precomp T hT V i j hij f).mp (Subsingleton.elim _ _)

end CategoryTheory.Pretriangulated
