/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenBoundedCandidate

/-! # Original open-reconstruction coordinate squares before local realization -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- The original stage square, named before any coherent model is specialized. -/
def ReconstructionStageSquare {C : Type*} [Category C] {A B D H : C}
    (s : A ⟶ B) (f : B ⟶ D) (a : A ⟶ H) (u : H ⟶ D) : Prop :=
  s ≫ f = a ≫ u

/-- Cancel only the original right coordinate isomorphism, before specializing
any reconstructed coherent object. -/
theorem reconstructionStageSquare_of_right_iso {C : Type*} [Category C]
    {A B D E H : C} (s : A ⟶ B) (a : A ⟶ H) (f : B ⟶ D)
    (e : D ⟶ E) [Mono e] (u : H ⟶ D) (v : H ⟶ E)
    (hs : s ≫ (f ≫ e) = a ≫ v) (hu : u ≫ e = v) :
    ReconstructionStageSquare s f a u := by
  change s ≫ f = a ≫ u
  apply (cancel_mono e).mp
  simpa only [Category.assoc, hu] using hs

universe u

/-- Undo only the original completion comparison for arbitrary local stage data. -/
theorem openReconstructionStages_square
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ X) [IsOpenImmersion p]
    {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}
    (α : F ⟶ (completionFunctor X K).obj H)
    (G : Y.Modules) (a : G ⟶ (pullback p).obj H.obj)
    (s : (Functor.const ℕᵒᵖ).obj G ⟶ F.obj ⋙ pullback p)
    (hs : ∀ n : ℕᵒᵖ, s.app n ≫ (openReconstructionComparison p α).hom.app n =
      a ≫ (idealSheafQuotientUnit Y (K.comap p ^ n.unop)).app
        ((pullback p).obj H.obj)) (n : ℕᵒᵖ) :
    ReconstructionStageSquare (s.app n) ((pullback p).map (α.hom.app n)) a
      ((pullback p).map ((idealSheafQuotientUnit X (K ^ n.unop)).app H.obj)) := by
  rcases n with ⟨k⟩
  refine reconstructionStageSquare_of_right_iso (s.app (op k)) a
    ((pullback p).map (α.hom.app (op k)))
    ((openIdealPullbackCompletionIso p K H).hom.hom.app (op k))
    ((pullback p).map ((idealSheafQuotientUnit X (K ^ k)).app H.obj))
    ((idealSheafQuotientUnit Y (K.comap p ^ k)).app ((pullback p).obj H.obj))
    (hs (op k)) ?_
  exact openIdealPullbackCompletionIso_unit p K H k

end AlgebraicGeometry.Scheme.Modules.Coherent
