/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateEmbedding
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionSubobjectIso
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CandidateIsoComparison

/-! # Assembly from actual local bounded-candidate comparisons

The constructor consumes whole local isomorphism certificates before any affine
reconstruction is specialized. The ambient remains the original pullback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u v

/-- Whole local target-and-stage comparisons assemble in the original ambient. -/
def boundedCandidateIsoOfLocalComparisons
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type v} (Y : ι → Scheme.{u}) [∀ i, IsLocallyNoetherian (Y i)]
    (p : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (p i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), p i y = x)
    {K : X.IdealSheafData} {F : AdicSystem X K} {H G₁ G₂ : X.CoherentSheaf}
    (α : F ⟶ (completionFunctor X K).obj H)
    (a₁ : G₁ ⟶ H) (β₁ : (completionFunctor X K).obj G₁ ≅ F)
    (h₁ : β₁.hom ≫ α = (completionFunctor X K).map a₁)
    (a₂ : G₂ ⟶ H) (β₂ : (completionFunctor X K).obj G₂ ≅ F)
    (h₂ : β₂.hom ≫ α = (completionFunctor X K).map a₂)
    [Mono (boundedCandidateLift α a₂ β₂ h₂)]
    (e : ∀ i, CandidateIsoComparison ((coherentPullback (p i)).map a₁)
      (openReconstructionCandidateIso (p i) β₁) ((coherentPullback (p i)).map a₂)
      (openReconstructionCandidateIso (p i) β₂)) :
    CandidateIsoComparison a₁ β₁ a₂ β₂ := by
  let s := boundedCandidateLift α a₁ β₁ h₁
  let t := boundedCandidateLift α a₂ β₂ h₂
  have hp (i : ι) : (pullback (p i)).map s =
      (e i).val.hom.hom ≫ (pullback (p i)).map t := by
    let : PreservesLimitsOfShape ℕᵒᵖ (pullback (p i)) :=
      preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback (p i))
    let : PreservesLimitsOfShape WalkingCospan (pullback (p i)) :=
      preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback (p i))
    dsimp only [s, t]
    apply reconstructionMapped_hom_ext (pullback (p i)) α
    · simp only [Category.assoc, ← Functor.map_comp,
        boundedCandidateLift_toTarget]
      have he := (congrArg (fun f => f.hom) (e i).property.1).symm
      change (pullback (p i)).map a₁.hom =
        (e i).val.hom.hom ≫ (pullback (p i)).map a₂.hom at he
      exact he
    · intro n
      simp only [Category.assoc, ← Functor.map_comp,
        boundedCandidateLift_toStage]
      change (pullback (p i)).map
          ((idealSheafQuotientUnit X (K ^ n.unop)).app G₁.obj ≫ β₁.hom.hom.app n) =
        (e i).val.hom.hom ≫ (pullback (p i)).map
          ((idealSheafQuotientUnit X (K ^ n.unop)).app G₂.obj ≫ β₂.hom.hom.app n)
      rw [← openReconstructionCandidateIso_stage (p i) β₁ n.unop,
        ← openReconstructionCandidateIso_stage (p i) β₂ n.unop]
      exact ((e i).property.2 n.unop).symm
  let c (i : ι) : G₁.obj.restrict (p i) ≅ G₂.obj.restrict (p i) :=
    (restrictFunctorIsoPullback (p i)).app G₁.obj ≪≫
      (QuasiCoherent.finiteTypeSheavesToModules (Y i)).mapIso (e i).val ≪≫
        ((restrictFunctorIsoPullback (p i)).app G₂.obj).symm
  have hc (i : ι) : (restrictFunctor (p i)).map s =
      (c i).hom ≫ (restrictFunctor (p i)).map t := by
    apply (cancel_mono ((restrictFunctorIsoPullback (p i)).hom.app
      (reconstructionPullback α))).mp
    rw [(restrictFunctorIsoPullback (p i)).hom.naturality, hp i]
    dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Iso.app_hom, Iso.app_inv, Category.assoc]
    rw [← (restrictFunctorIsoPullback (p i)).inv.naturality_assoc t]
    simp only [Iso.inv_hom_id_app, Category.comp_id]
    rfl
  let d := reconstructionSubobjectIsoOfOpenCover Y p
    hcover s t c hc
  let E : G₁ ≅ G₂ := ObjectProperty.isoMk _ d.val
  refine ⟨E, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    change d.val.hom ≫ a₂.hom = a₁.hom
    have he := congrArg (fun f => f ≫ reconstructionToTarget α) d.property
    simpa only [s, t, Category.assoc, boundedCandidateLift_toTarget] using he.symm
  · intro n
    change d.val.hom ≫ (idealSheafQuotientUnit X (K ^ n)).app G₂.obj ≫
      β₂.hom.hom.app (op n) =
        (idealSheafQuotientUnit X (K ^ n)).app G₁.obj ≫ β₁.hom.hom.app (op n)
    have he := congrArg (fun f => f ≫ reconstructionToStage α (op n)) d.property
    simpa only [s, t, Category.assoc, boundedCandidateLift_toStage, boundedCandidateStages,
      NatTrans.comp_app, idealSheafQuotientTowerUnit] using he.symm

end AlgebraicGeometry.Scheme.Modules.Coherent
