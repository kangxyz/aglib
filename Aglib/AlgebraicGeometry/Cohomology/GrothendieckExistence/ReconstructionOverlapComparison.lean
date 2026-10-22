/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenOverlapCoordinates
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateTransport

/-! # Genuine bounded-candidate comparison on arbitrary open overlaps

The overlap need not be affine. Both already algebraic candidates are restricted
to it and compared by global bounded-candidate uniqueness, independently of
existence. Every target and original finite-stage projection is retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X U V : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
  (p : U ⟶ X) (q : V ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q]
  (K : X.IdealSheafData)

local instance : IsLocallyNoetherian (Limits.pullback p q) :=
  isLocallyNoetherian_of_isOpenImmersion (pullback.fst p q)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
  [IsOpenImmersion p] [IsOpenImmersion q] in
/-- The two overlap ideals are the actual equal inverse-image ideals. -/
theorem reconstructionOverlapIdealEq :
    (K.comap p).comap (pullback.fst p q) =
      (K.comap q).comap (pullback.snd p q) := by
  rw [← K.comap_comp, ← K.comap_comp, pullback.condition]

/-- Completion coordinates on the actual overlap, retaining the native
restriction gluer's comparison rather than an independently chosen comparison. -/
def reconstructionOverlapCompletionIso (H : X.CoherentSheaf) :
    idealSheafQuotientTower (Limits.pullback p q) ((K.comap p).comap (pullback.fst p q))
        ((pullback (pullback.fst p q)).obj ((pullback p).obj H.obj)) ≅
      idealSheafQuotientTower (Limits.pullback p q) ((K.comap q).comap (pullback.snd p q))
        ((pullback (pullback.snd p q)).obj ((pullback q).obj H.obj)) :=
  (iteratedOpenCompletionDiagramIso (pullback.fst p q) p K H).symm ≪≫
    Functor.isoWhiskerLeft (idealSheafQuotientTower X K H.obj)
      (reconstructionOverlapPullbackIso p q) ≪≫
        iteratedOpenCompletionDiagramIso (pullback.snd p q) q K H

/-- The comparison preserves the actual quotient units on the overlap. -/
@[reassoc]
theorem reconstructionOverlapCompletionIso_unit (H : X.CoherentSheaf) (n : ℕ) :
    (idealSheafQuotientUnit (Limits.pullback p q)
      ((K.comap p).comap (pullback.fst p q) ^ n)).app
        ((pullback (pullback.fst p q)).obj ((pullback p).obj H.obj)) ≫
      (reconstructionOverlapCompletionIso p q K H).hom.app (op n) =
    (reconstructionOverlapPullbackIso p q).hom.app H.obj ≫
      (idealSheafQuotientUnit (Limits.pullback p q)
        ((K.comap q).comap (pullback.snd p q) ^ n)).app
          ((pullback (pullback.snd p q)).obj ((pullback q).obj H.obj)) := by
  change _ ≫ (iteratedOpenCompletionDiagramIso (pullback.fst p q) p K H).inv.app
      (op n) ≫ (reconstructionOverlapPullbackIso p q).hom.app
        ((idealSheafQuotientTower X K H.obj).obj (op n)) ≫
          (iteratedOpenCompletionDiagramIso (pullback.snd p q) q K H).hom.app
            (op n) = _
  have hn : (pullback (pullback.fst p q)).map ((pullback p).map
      ((idealSheafQuotientUnit X (K ^ n)).app H.obj)) ≫
        (reconstructionOverlapPullbackIso p q).hom.app
          ((idealSheafQuotientTower X K H.obj).obj (op n)) =
      (reconstructionOverlapPullbackIso p q).hom.app H.obj ≫
        (pullback (pullback.snd p q)).map ((pullback q).map
          ((idealSheafQuotientUnit X (K ^ n)).app H.obj)) :=
    (reconstructionOverlapPullbackIso p q).hom.naturality
      ((idealSheafQuotientUnit X (K ^ n)).app H.obj)
  rw [← Category.assoc, ← Category.assoc, iteratedOpenCompletionDiagramIso_inv_unit,
    hn, Category.assoc, iteratedOpenCompletionDiagramIso_unit]

variable {K} {F : AdicSystem X K} {H : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)

/-- The overlap square is the original naturality square of the formal map. -/
theorem reconstructionOverlapComparison_square :
    (openReconstructionComparison (pullback.fst p q)
      (openReconstructionComparison p α)).hom ≫
        (reconstructionOverlapCompletionIso p q K H).hom =
      (Functor.isoWhiskerLeft F.obj (reconstructionOverlapPullbackIso p q)).hom ≫
        (openReconstructionComparison (pullback.snd p q)
          (openReconstructionComparison q α)).hom := by
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app, iteratedOpenReconstructionComparison_app]
  change (_ ≫ (iteratedOpenCompletionDiagramIso (pullback.fst p q) p K H).hom.app n) ≫
    ((iteratedOpenCompletionDiagramIso (pullback.fst p q) p K H).inv.app n ≫
      (reconstructionOverlapPullbackIso p q).hom.app _ ≫
        (iteratedOpenCompletionDiagramIso (pullback.snd p q) q K H).hom.app n) = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (reconstructionOverlapPullbackIso p q).hom.naturality_assoc (α.hom.app n) _

/-- The whole original overlap comparison, before specializing a bounded producer. -/
def reconstructionOverlapCandidateComparison
    {G₁ : U.CoherentSheaf} {G₂ : V.CoherentSheaf}
    (a₁ : G₁ ⟶ (coherentPullback p).obj H)
    (β₁ : (completionFunctor U (K.comap p)).obj G₁ ≅
      (openIdealPullbackFunctor p K).obj F)
    (a₂ : G₂ ⟶ (coherentPullback q).obj H)
    (β₂ : (completionFunctor V (K.comap q)).obj G₂ ≅
      (openIdealPullbackFunctor q K).obj F) :=
    {e : (coherentPullback (pullback.fst p q)).obj G₁ ≅
      (coherentPullback (pullback.snd p q)).obj G₂ //
      e.hom.hom ≫ (pullback (pullback.snd p q)).map a₂.hom =
        (pullback (pullback.fst p q)).map a₁.hom ≫
          (reconstructionOverlapPullbackIso p q).hom.app H.obj ∧ ∀ n : ℕ,
      e.hom.hom ≫ (pullback (pullback.snd p q)).map
        ((idealSheafQuotientUnit V (K.comap q ^ n)).app G₂.obj ≫
          β₂.hom.hom.app (op n)) =
      (pullback (pullback.fst p q)).map
        ((idealSheafQuotientUnit U (K.comap p ^ n)).app G₁.obj ≫
          β₁.hom.hom.app (op n)) ≫
        (reconstructionOverlapPullbackIso p q).hom.app (F.obj.obj (op n))}

/-- Convert a whole transported comparison to the original overlap stages. -/
def reconstructionOverlapCandidateComparisonOfTransport
    {G₁ : U.CoherentSheaf} {G₂ : V.CoherentSheaf}
    (a₁ : G₁ ⟶ (coherentPullback p).obj H)
    (β₁ : (completionFunctor U (K.comap p)).obj G₁ ≅
      (openIdealPullbackFunctor p K).obj F)
    (a₂ : G₂ ⟶ (coherentPullback q).obj H)
    (β₂ : (completionFunctor V (K.comap q)).obj G₂ ≅
      (openIdealPullbackFunctor q K).obj F)
    (d : CandidateIsoTransportComparison
      (Functor.isoWhiskerLeft F.obj (reconstructionOverlapPullbackIso p q))
      (ObjectProperty.isoMk _ ((reconstructionOverlapPullbackIso p q).app H.obj))
      ((coherentPullback (pullback.fst p q)).map a₁)
      (openReconstructionCandidateIso (pullback.fst p q) β₁)
      ((coherentPullback (pullback.snd p q)).map a₂)
      (openReconstructionCandidateIso (pullback.snd p q) β₂)) :
    reconstructionOverlapCandidateComparison p q a₁ β₁ a₂ β₂ := by
  refine ⟨d.val, congrArg (fun f => f.hom) d.property.1, ?_⟩
  intro n
  rw [← openReconstructionCandidateIso_stage (pullback.snd p q) β₂ n,
    ← openReconstructionCandidateIso_stage (pullback.fst p q) β₁ n]
  have hd := d.property.2 n
  change d.val.hom.hom ≫
      (idealSheafQuotientUnit (Limits.pullback p q)
        ((K.comap q).comap (pullback.snd p q) ^ n)).app
          ((pullback (pullback.snd p q)).obj G₂.obj) ≫
        (openReconstructionCandidateIso (pullback.snd p q) β₂).hom.hom.app (op n) =
    (idealSheafQuotientUnit (Limits.pullback p q)
      ((K.comap p).comap (pullback.fst p q) ^ n)).app
        ((pullback (pullback.fst p q)).obj G₁.obj) ≫
      (openReconstructionCandidateIso (pullback.fst p q) β₁).hom.hom.app (op n) ≫
        (reconstructionOverlapPullbackIso p q).hom.app (F.obj.obj (op n)) at hd
  simpa only [Category.assoc] using hd

/-- The genuine overlap isomorphism preserves the original target and every
original stage, with only the actual same-ideal ordinary defect bounds. -/
def reconstructionOverlapCandidateIso
    {G₁ : U.CoherentSheaf} {G₂ : V.CoherentSheaf}
    (a₁ : G₁ ⟶ (coherentPullback p).obj H)
    (β₁ : (completionFunctor U (K.comap p)).obj G₁ ≅
      (openIdealPullbackFunctor p K).obj F)
    (h₁ : β₁.hom ≫ openReconstructionComparison p α =
      (completionFunctor U (K.comap p)).map a₁)
    (t₁ : ℕ) (hk₁ : killedByIdealSheaf (K.comap p ^ t₁) (kernel a₁.hom))
    (hc₁ : killedByIdealSheaf (K.comap p ^ t₁) (cokernel a₁.hom))
    (a₂ : G₂ ⟶ (coherentPullback q).obj H)
    (β₂ : (completionFunctor V (K.comap q)).obj G₂ ≅
      (openIdealPullbackFunctor q K).obj F)
    (h₂ : β₂.hom ≫ openReconstructionComparison q α =
      (completionFunctor V (K.comap q)).map a₂)
    (t₂ : ℕ) (hk₂ : killedByIdealSheaf (K.comap q ^ t₂) (kernel a₂.hom))
    (hc₂ : killedByIdealSheaf (K.comap q ^ t₂) (cokernel a₂.hom)) :
    reconstructionOverlapCandidateComparison p q a₁ β₁ a₂ β₂ := by
  let eH : (coherentPullback (pullback.fst p q)).obj ((coherentPullback p).obj H) ≅
      (coherentPullback (pullback.snd p q)).obj ((coherentPullback q).obj H) :=
    ObjectProperty.isoMk _ ((reconstructionOverlapPullbackIso p q).app H.obj)
  let d := boundedCandidateIsoAcrossIdeals (reconstructionOverlapIdealEq p q K)
    (openReconstructionComparison (pullback.fst p q) (openReconstructionComparison p α))
    (openReconstructionComparison (pullback.snd p q) (openReconstructionComparison q α))
    (Functor.isoWhiskerLeft F.obj (reconstructionOverlapPullbackIso p q)) eH
    (reconstructionOverlapCompletionIso p q K H)
    (reconstructionOverlapCompletionIso_unit p q K H)
    (reconstructionOverlapComparison_square p q α)
    ((coherentPullback (pullback.fst p q)).map a₁)
    (openReconstructionCandidateIso (pullback.fst p q) β₁)
    (openReconstructionCandidateIso_square (pullback.fst p q)
      (openReconstructionComparison p α) a₁ β₁ h₁) t₁
    (openReconstructionCandidate_bounds (pullback.fst p q) a₁ t₁ hk₁ hc₁).1
    (openReconstructionCandidate_bounds (pullback.fst p q) a₁ t₁ hk₁ hc₁).2
    ((coherentPullback (pullback.snd p q)).map a₂)
    (openReconstructionCandidateIso (pullback.snd p q) β₂)
    (openReconstructionCandidateIso_square (pullback.snd p q)
      (openReconstructionComparison q α) a₂ β₂ h₂) t₂
    (openReconstructionCandidate_bounds (pullback.snd p q) a₂ t₂ hk₂ hc₂).1
    (openReconstructionCandidate_bounds (pullback.snd p q) a₂ t₂ hk₂ hc₂).2
  exact reconstructionOverlapCandidateComparisonOfTransport p q a₁ β₁ a₂ β₂ d

end AlgebraicGeometry.Scheme.Modules.Coherent
