/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Large-site left Kan extension of abelian presheaves

Generic inverse-image exactness foundation for
`K2-018#eq:k2018-pointed-character`, at frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Universe-generalized versions of the pointwise argument in pinned mathlib
`CategoryTheory/Functor/Flat.lean`, `lanEvaluationIsoColim` and
`lan_preservesFiniteLimits_of_flat` (Andrew Yang). The existing versions require
small categories with equal object and morphism universes. Small étale sites
are large categories, so we keep both universes and raise the group universe.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor.LargePresheaf
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise left Kan extension at an object, for large abelian presheaves. -/
def lanEvaluationIsoColim (F : C ⥤ D) (X : D) :
    F.lan ⋙ (evaluation D AddCommGrpCat.{max u v}).obj X ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{max u v}).obj
        (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ AddCommGrpCat.{max u v}) =>
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
        (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

/-- Flat left Kan extension of large abelian presheaves preserves finite limits. -/
theorem lan_preservesFiniteLimits (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits
      (F.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{max u v}) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max u v}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    (F.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{max u v}) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  have : ReflectsLimits (CategoryTheory.forget AddCommGrpCat.{max u v}) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFilteredColimitsOfSize.{v, max u v}
      (CategoryTheory.forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink (CategoryTheory.forget AddCommGrpCat.{max u v})
  have : PreservesColimitsOfShape (CostructuredArrow F.op K)
      (CategoryTheory.forget AddCommGrpCat.{max u v}) := by infer_instance
  have : PreservesLimitsOfShape J
      (colim : (CostructuredArrow F.op K ⥤ AddCommGrpCat.{max u v}) ⥤ _) := by
    infer_instance
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _).symm

end CategoryTheory.Functor.LargePresheaf

namespace CategoryTheory.Functor.LargePresheaf
section TypeKan
universe a b
variable {C D : Type a} [Category.{b} C] [Category.{b} D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise left Kan extension at an object, for large set-valued presheaves. -/
def typeLanEvaluationIsoColim (F : C ⥤ D) (X : D) :
    F.lan ⋙ (evaluation D (Type (max a b))).obj X ≅
      (Functor.whiskeringLeft _ _ (Type (max a b))).obj
        (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ (Type (max a b))) =>
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
        (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

/-- Flat left Kan extension of large set-valued presheaves preserves finite limits. -/
theorem typeLan_preservesFiniteLimits (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits
      (F.op.lan : (Cᵒᵖ ⥤ (Type (max a b))) ⥤ Dᵒᵖ ⥤ (Type (max a b))) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max a b}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    (F.op.lan : (Cᵒᵖ ⥤ (Type (max a b))) ⥤ Dᵒᵖ ⥤ (Type (max a b))) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  have : PreservesLimitsOfShape J
      (colim : (CostructuredArrow F.op K ⥤ (Type (max a b))) ⥤ _) := by
    infer_instance
  exact preservesLimitsOfShape_of_natIso (typeLanEvaluationIsoColim _ _).symm

end TypeKan

end CategoryTheory.Functor.LargePresheaf

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 1a17ebc153770d0fd29087747b013c4c124becf502ea25b4870266b058e3738c.
Definitions, hypotheses and universes are retained modulo native names. -/
