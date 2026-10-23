/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.Flat

/-! # Flat Kan extensions with independent category universes

The native pointwise left Kan extension computes evaluation by the original
costructured-arrow colimit. Its filtered-colimit proof of finite-limit
preservation does not require the source and target to be small categories
in the same universe. Size and preservation assumptions on those actual
colimits are explicit.

The argument generalizes the native `lanEvaluationIsoColim` and
`lan_preservesFiniteLimits_of_flat` proofs, retaining their pointwise Kan
extension and colimit maps rather than choosing another extension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v' a b

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (E : Type a) [Category.{b} E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation of the original left Kan extension at an object, at independent
source, target and value sizes. -/
def lanEvaluationIsoColimitOfShape (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

variable {FE : E → E → Type*} {CE : E → Type b}
  [instFunLike : ∀ X Y, FunLike (FE X Y) (CE X) (CE Y)]
  [instConcrete : ConcreteCategory.{b} E FE]
  [instLimits : HasLimits E] [instReflects : ReflectsLimits (forget E)]
  [instPreserves : PreservesLimits (forget E)]
  (F : C ⥤ D) [RepresentablyFlat F]
  [instColimits : ∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow F.op X) E]
  [instSmall : ∀ X : Dᵒᵖ, Small.{b} (CostructuredArrow F.op X)]
  [instColimPreserves : ∀ X : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op X) (forget E)]

include instConcrete instLimits instReflects instPreserves instColimits instSmall instColimPreserves

/-- The original flat left Kan extension preserves finite limits with explicit
actual colimit-size hypotheses, without equal category universes. -/
theorem lan_preservesFiniteLimits_of_flat_of_shapes :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{0}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro X
  let : IsFiltered (CostructuredArrow F.op X) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop X))
  let : PreservesLimitsOfShape J (colim : (CostructuredArrow F.op X ⥤ E) ⥤ E) :=
    filtered_colim_preservesFiniteLimits (C := E) (FC := FE) (CC := CE)
      (J := J) (K := CostructuredArrow F.op X)
  let : PreservesLimitsOfShape J
      ((Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F.op X)) := inferInstance
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColimitOfShape E F.op X).symm

end CategoryTheory.Functor
