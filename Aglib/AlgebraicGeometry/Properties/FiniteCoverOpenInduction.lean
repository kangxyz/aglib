/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Finite-cover induction on the opens of one original scheme -/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (P : X.Opens → Prop)
  (hAffine : ∀ U : X.Opens, IsAffineOpen U → P U)
  (hCover : ∀ {ι : Type u} [Finite ι] (U : ι → X.Opens),
    (∀ i, P (U i)) → (∀ i j, P (U i ⊓ U j)) → P (iSup U))

include hCover in
/-- Binary gluing is a special case of gluing on the original finite family. -/
theorem of_sup_of_finiteCover (U V : X.Opens) (hU : P U) (hV : P V)
    (hUV : P (U ⊓ V)) : P (U ⊔ V) := by
  let W : ULift.{u} Bool → X.Opens := fun i => if i.down then U else V
  have hW : ∀ i, P (W i) := by
    intro ⟨i⟩
    cases i
    · simpa [W] using hV
    · simpa [W] using hU
  have hWW : ∀ i j, P (W i ⊓ W j) := by
    intro ⟨i⟩ ⟨j⟩
    cases i <;> cases j
    · simpa [W] using hV
    · simpa [W, inf_comm] using hUV
    · simpa [W] using hUV
    · simpa [W] using hU
  simpa only [W, iSup_ulift, iSup_bool_eq, Bool.false_eq_true, ↓reduceIte] using hCover W hW hWW

include hAffine hCover in
/-- A compact separated open is covered by finitely many affine opens whose
original images and pairwise intersections in the ambient scheme are affine. -/
theorem of_compact_separated_open_of_finiteCover (U : X.Opens)
    [U.toScheme.IsSeparated] (hU : IsCompact (U : Set X)) : P U := by
  classical
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨s, hs, htop⟩ :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (show IsCompact ((⊤ : U.toScheme.Opens) : Set U.toScheme) from isCompact_univ)
  let : Fintype s := hs.fintype
  let V : s → X.Opens := fun i => U.ι ''ᵁ i.val.val
  have hi : ∀ i : s, P (V i) := fun i =>
    hAffine _ (i.val.property.image_of_isOpenImmersion U.ι)
  have hij : ∀ i j : s, P (V i ⊓ V j) := by
    intro i j
    have he : V i ⊓ V j = U.ι ''ᵁ (i.val.val ⊓ j.val.val) := by
      apply Opens.ext
      exact (Set.image_inter U.ι.isOpenEmbedding.injective).symm
    rw [he]
    exact hAffine _ ((i.val.property.inf j.val.property).image_of_isOpenImmersion U.ι)
  have hsup : iSup V = U := by
    dsimp only [V]
    rw [← U.ι.image_iSup]
    have he : (⨆ i : s, i.val.val) = ⊤ := by
      simpa only [iSup_subtype] using htop.symm
    rw [he, U.ι.image_top_eq_opensRange, Opens.opensRange_ι]
  rw [← hsup]
  exact hCover V hi hij

include hAffine hCover in
/-- On a quasi-separated scheme, the affine case and finite-cover gluing
imply the property on every compact open, without changing the ambient scheme. -/
theorem of_compact_open_of_finiteCover [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : P U := by
  refine compact_open_induction_on U hU (hAffine _ (isAffineOpen_bot X)) ?_
  intro S hS V ih
  let : IsAffine V.val.toScheme := V.property
  let i : (S ⊓ V.val).toScheme ⟶ V.val.toScheme := X.homOfLE inf_le_right
  let : (S ⊓ V.val).toScheme.IsSeparated := ⟨by
    rw [← terminal.comp_from i]
    infer_instance⟩
  have hSV : IsCompact ((S ⊓ V.val : X.Opens) : Set X) :=
    hS.inter_of_isOpen V.property.isCompact S.isOpen V.val.isOpen
  exact of_sup_of_finiteCover P hCover S V.val ih (hAffine _ V.property)
    (of_compact_separated_open_of_finiteCover P hAffine hCover _ hSV)

end AlgebraicGeometry.Scheme
