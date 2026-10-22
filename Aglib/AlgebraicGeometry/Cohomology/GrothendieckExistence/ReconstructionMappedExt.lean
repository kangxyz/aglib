/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionMappedLift

/-! # Original projection extensionality after restriction

The ambient need not be quasicoherent. Preservation of its defining limits
retains the joint monicity of the original algebraic and formal projections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian X]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}
  (T : X.Modules ⥤ Y.Modules) [PreservesLimitsOfShape ℕᵒᵖ T]
  [PreservesLimitsOfShape WalkingCospan T]
  (α : F ⟶ (completionFunctor X K).obj H)

/-- The original mapped algebraic projection and every original mapped formal
projection jointly detect equality, for an arbitrary module-sheaf source. -/
theorem reconstructionMapped_hom_ext {M : Y.Modules}
    (f g : M ⟶ T.obj (reconstructionPullback α))
    (ha : f ≫ T.map (reconstructionToTarget α) = g ≫ T.map (reconstructionToTarget α))
    (hs : ∀ n, f ≫ T.map (reconstructionToStage α n) =
      g ≫ T.map (reconstructionToStage α n)) : f = g := by
  apply (cancel_mono (PreservesPullback.iso T (limMap α.hom)
    (completionLimitUnit K H)).hom).mp
  apply pullback.hom_ext
  · apply (isLimitOfPreserves T (limit.isLimit F.obj)).hom_ext
    intro n
    change _ ≫ T.map ((limit.cone F.obj).π.app n) =
      _ ≫ T.map ((limit.cone F.obj).π.app n)
    rw [limit.cone_π]
    simpa only [Category.assoc, PreservesPullback.iso_hom_fst,
      ← Functor.map_comp, reconstructionToStage] using hs n
  · simpa only [Category.assoc, PreservesPullback.iso_hom_snd,
      reconstructionToTarget] using ha

end AlgebraicGeometry.Scheme.Modules.Coherent
