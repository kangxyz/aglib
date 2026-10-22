/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateEmbedding

/-! # Original target-and-stage uniqueness without a chosen cover -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H G A : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (a : G ⟶ H) (β : (completionFunctor X K).obj G ≅ F)
  (hβ : β.hom ≫ α = (completionFunctor X K).map a)

include hβ in
/-- Global maps into a genuine bounded candidate are determined by their
original target and every specified formal stage. -/
theorem boundedCandidate_hom_ext (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (cokernel a.hom))
    (f g : A ⟶ G) (ha : f ≫ a = g ≫ a)
    (hs : ∀ n : ℕ,
      f.hom ≫ (idealSheafQuotientUnit X (K ^ n)).app G.obj ≫ β.hom.hom.app (op n) =
      g.hom ≫ (idealSheafQuotientUnit X (K ^ n)).app G.obj ≫ β.hom.hom.app (op n)) :
    f = g := by
  let := boundedCandidateLift_mono α a β hβ t hk hc
  apply ObjectProperty.hom_ext
  apply (cancel_mono (boundedCandidateLift α a β hβ)).mp
  apply reconstructionPullback_hom_ext α
  · simp only [Category.assoc, boundedCandidateLift_toTarget]
    exact congrArg (fun q => q.hom) ha
  · intro n
    simp only [Category.assoc, boundedCandidateLift_toStage]
    exact hs n.unop

end AlgebraicGeometry.Scheme.Modules.Coherent
